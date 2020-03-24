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
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4204 =
                match uu____4204 with
                | (f',uu____4210) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4212 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4212
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
              (let uu____4222 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4222);
              (match () with | () -> record)))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4270 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4277 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4278 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4280,pats1) ->
            let aux out uu____4321 =
              match uu____4321 with
              | (p1,uu____4334) ->
                  let intersection =
                    let uu____4344 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4344 out  in
                  let uu____4347 = FStar_Util.set_is_empty intersection  in
                  if uu____4347
                  then
                    let uu____4352 = pat_vars p1  in
                    FStar_Util.set_union out uu____4352
                  else
                    (let duplicate_bv =
                       let uu____4358 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4358  in
                     let uu____4361 =
                       let uu____4367 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4367)
                        in
                     FStar_Errors.raise_error uu____4361 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4391 = pat_vars p  in
          FStar_All.pipe_right uu____4391 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4419 =
              let uu____4421 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4421  in
            if uu____4419
            then ()
            else
              (let nonlinear_vars =
                 let uu____4430 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4430  in
               let first_nonlinear_var =
                 let uu____4434 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4434  in
               let uu____4437 =
                 let uu____4443 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4443)  in
               FStar_Errors.raise_error uu____4437 r)
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
          let uu____4758 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4758 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4775 ->
              let uu____4778 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4778 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4919 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4941 =
                  let uu____4947 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4947, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4941  in
              let p2 =
                let uu___934_4952 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_4952.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4969 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4972 = aux loc env1 p2  in
                match uu____4972 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5028 =
                      match binder with
                      | LetBinder uu____5049 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5074 = close_fun env1 t  in
                            desugar_term env1 uu____5074  in
                          let x1 =
                            let uu___960_5076 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5076.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5076.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5028 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5122 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5123 -> ()
                           | uu____5124 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5125 ->
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
              let uu____5143 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5143, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5156 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5156, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5174 = resolvex loc env1 x  in
              (match uu____5174 with
               | (loc1,env2,xbv) ->
                   let uu____5206 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5206, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5224 = resolvex loc env1 x  in
              (match uu____5224 with
               | (loc1,env2,xbv) ->
                   let uu____5256 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5256, []))
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
              let uu____5270 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5270, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5298;_},args)
              ->
              let uu____5304 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5365  ->
                       match uu____5365 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5446 = aux loc1 env2 arg  in
                           (match uu____5446 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5304 with
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
                   let uu____5618 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5618, annots))
          | FStar_Parser_AST.PatApp uu____5634 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5662 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5712  ->
                       match uu____5712 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5773 = aux loc1 env2 pat  in
                           (match uu____5773 with
                            | (loc2,env3,uu____5812,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5662 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5906 =
                       let uu____5909 =
                         let uu____5916 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5916  in
                       let uu____5917 =
                         let uu____5918 =
                           let uu____5932 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5932, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5918  in
                       FStar_All.pipe_left uu____5909 uu____5917  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5966 =
                              let uu____5967 =
                                let uu____5981 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5981, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5967  in
                            FStar_All.pipe_left (pos_r r) uu____5966) pats1
                       uu____5906
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
              let uu____6037 =
                FStar_List.fold_left
                  (fun uu____6096  ->
                     fun p2  ->
                       match uu____6096 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6178 = aux loc1 env2 p2  in
                           (match uu____6178 with
                            | (loc2,env3,uu____6222,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6037 with
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
                     | uu____6385 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6388 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6388, annots))
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
                     (fun uu____6464  ->
                        match uu____6464 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6494  ->
                        match uu____6494 with
                        | (f,uu____6500) ->
                            let uu____6501 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6527  ->
                                      match uu____6527 with
                                      | (g,uu____6534) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6501 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6540,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6547 =
                  let uu____6548 =
                    let uu____6555 =
                      let uu____6556 =
                        let uu____6557 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6557  in
                      FStar_Parser_AST.mk_pattern uu____6556
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6555, args)  in
                  FStar_Parser_AST.PatApp uu____6548  in
                FStar_Parser_AST.mk_pattern uu____6547
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6560 = aux loc env1 app  in
              (match uu____6560 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6637 =
                           let uu____6638 =
                             let uu____6652 =
                               let uu___1110_6653 = fv  in
                               let uu____6654 =
                                 let uu____6657 =
                                   let uu____6658 =
                                     let uu____6665 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6665)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6658
                                    in
                                 FStar_Pervasives_Native.Some uu____6657  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6653.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6653.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6654
                               }  in
                             (uu____6652, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6638  in
                         FStar_All.pipe_left pos uu____6637
                     | uu____6691 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6775 = aux' true loc env1 p2  in
              (match uu____6775 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6828 =
                     FStar_List.fold_left
                       (fun uu____6876  ->
                          fun p4  ->
                            match uu____6876 with
                            | (loc2,env3,ps1) ->
                                let uu____6941 = aux' true loc2 env3 p4  in
                                (match uu____6941 with
                                 | (loc3,env4,uu____6979,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6828 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7140 ->
              let uu____7141 = aux' true loc env1 p1  in
              (match uu____7141 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7232 = aux_maybe_or env p  in
        match uu____7232 with
        | (env1,b,pats) ->
            ((let uu____7287 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7287
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
            let uu____7361 =
              let uu____7362 =
                let uu____7373 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7373, (ty, tacopt))  in
              LetBinder uu____7362  in
            (env, uu____7361, [])  in
          let op_to_ident x =
            let uu____7390 =
              let uu____7396 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7396, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7390  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7409 = op_to_ident x  in
              mklet uu____7409 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7411) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7417;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7433 = op_to_ident x  in
              let uu____7434 = desugar_term env t  in
              mklet uu____7433 uu____7434 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7436);
                 FStar_Parser_AST.prange = uu____7437;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7457 = desugar_term env t  in
              mklet x uu____7457 tacopt1
          | uu____7458 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7471 = desugar_data_pat true env p  in
           match uu____7471 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7501;
                      FStar_Syntax_Syntax.p = uu____7502;_},uu____7503)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7516;
                      FStar_Syntax_Syntax.p = uu____7517;_},uu____7518)::[]
                     -> []
                 | uu____7531 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7539  ->
    fun env  ->
      fun pat  ->
        let uu____7543 = desugar_data_pat false env pat  in
        match uu____7543 with | (env1,uu____7560,pat1) -> (env1, pat1)

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
      let uu____7582 = desugar_term_aq env e  in
      match uu____7582 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7601 = desugar_typ_aq env e  in
      match uu____7601 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7611  ->
        fun range  ->
          match uu____7611 with
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
              ((let uu____7633 =
                  let uu____7635 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7635  in
                if uu____7633
                then
                  let uu____7638 =
                    let uu____7644 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7644)  in
                  FStar_Errors.log_issue range uu____7638
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
                  let uu____7665 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7665 range  in
                let lid1 =
                  let uu____7669 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7669 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7679 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7679 range  in
                           let private_fv =
                             let uu____7681 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7681 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7682 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7682.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7682.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7683 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7687 =
                        let uu____7693 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7693)
                         in
                      FStar_Errors.raise_error uu____7687 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7713 =
                  let uu____7720 =
                    let uu____7721 =
                      let uu____7738 =
                        let uu____7749 =
                          let uu____7758 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7758)  in
                        [uu____7749]  in
                      (lid1, uu____7738)  in
                    FStar_Syntax_Syntax.Tm_app uu____7721  in
                  FStar_Syntax_Syntax.mk uu____7720  in
                uu____7713 FStar_Pervasives_Native.None range))

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
          let uu___1293_7877 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7877.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7877.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7880 =
          let uu____7881 = unparen top  in uu____7881.FStar_Parser_AST.tm  in
        match uu____7880 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7886 ->
            let uu____7895 = desugar_formula env top  in (uu____7895, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7904 = desugar_formula env t  in (uu____7904, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7913 = desugar_formula env t  in (uu____7913, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7940 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7940, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7942 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7942, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7951 =
                let uu____7952 =
                  let uu____7959 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7959, args)  in
                FStar_Parser_AST.Op uu____7952  in
              FStar_Parser_AST.mk_term uu____7951 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7964 =
              let uu____7965 =
                let uu____7966 =
                  let uu____7973 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7973, [e])  in
                FStar_Parser_AST.Op uu____7966  in
              FStar_Parser_AST.mk_term uu____7965 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7964
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7985 = FStar_Ident.text_of_id op_star  in
             uu____7985 = "*") &&
              (let uu____7990 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7990 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8007;_},t1::t2::[])
                  when
                  let uu____8013 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8013 FStar_Option.isNone ->
                  let uu____8020 = flatten1 t1  in
                  FStar_List.append uu____8020 [t2]
              | uu____8023 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1341_8028 = top  in
              let uu____8029 =
                let uu____8030 =
                  let uu____8041 =
                    FStar_List.map (fun _8052  -> FStar_Util.Inr _8052) terms
                     in
                  (uu____8041, rhs)  in
                FStar_Parser_AST.Sum uu____8030  in
              {
                FStar_Parser_AST.tm = uu____8029;
                FStar_Parser_AST.range =
                  (uu___1341_8028.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1341_8028.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8060 =
              let uu____8061 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8061  in
            (uu____8060, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8067 =
              let uu____8073 =
                let uu____8075 =
                  let uu____8077 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8077 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8075  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8073)  in
            FStar_Errors.raise_error uu____8067 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8092 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8092 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8099 =
                   let uu____8105 =
                     let uu____8107 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8107
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8105)
                    in
                 FStar_Errors.raise_error uu____8099
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8122 =
                     let uu____8147 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8209 = desugar_term_aq env t  in
                               match uu____8209 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8147 FStar_List.unzip  in
                   (match uu____8122 with
                    | (args1,aqs) ->
                        let uu____8342 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8342, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8359)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8376 =
              let uu___1370_8377 = top  in
              let uu____8378 =
                let uu____8379 =
                  let uu____8386 =
                    let uu___1372_8387 = top  in
                    let uu____8388 =
                      let uu____8389 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8389  in
                    {
                      FStar_Parser_AST.tm = uu____8388;
                      FStar_Parser_AST.range =
                        (uu___1372_8387.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1372_8387.FStar_Parser_AST.level)
                    }  in
                  (uu____8386, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8379  in
              {
                FStar_Parser_AST.tm = uu____8378;
                FStar_Parser_AST.range =
                  (uu___1370_8377.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1370_8377.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8376
        | FStar_Parser_AST.Construct (n1,(a,uu____8397)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8417 =
                let uu___1382_8418 = top  in
                let uu____8419 =
                  let uu____8420 =
                    let uu____8427 =
                      let uu___1384_8428 = top  in
                      let uu____8429 =
                        let uu____8430 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8430  in
                      {
                        FStar_Parser_AST.tm = uu____8429;
                        FStar_Parser_AST.range =
                          (uu___1384_8428.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1384_8428.FStar_Parser_AST.level)
                      }  in
                    (uu____8427, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8420  in
                {
                  FStar_Parser_AST.tm = uu____8419;
                  FStar_Parser_AST.range =
                    (uu___1382_8418.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1382_8418.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8417))
        | FStar_Parser_AST.Construct (n1,(a,uu____8438)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8455 =
              let uu___1393_8456 = top  in
              let uu____8457 =
                let uu____8458 =
                  let uu____8465 =
                    let uu___1395_8466 = top  in
                    let uu____8467 =
                      let uu____8468 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8468  in
                    {
                      FStar_Parser_AST.tm = uu____8467;
                      FStar_Parser_AST.range =
                        (uu___1395_8466.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1395_8466.FStar_Parser_AST.level)
                    }  in
                  (uu____8465, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8458  in
              {
                FStar_Parser_AST.tm = uu____8457;
                FStar_Parser_AST.range =
                  (uu___1393_8456.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1393_8456.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8455
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8474; FStar_Ident.ident = uu____8475;
              FStar_Ident.nsstr = uu____8476; FStar_Ident.str = "Type0";_}
            ->
            let uu____8481 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8481, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8482; FStar_Ident.ident = uu____8483;
              FStar_Ident.nsstr = uu____8484; FStar_Ident.str = "Type";_}
            ->
            let uu____8489 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8489, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8490; FStar_Ident.ident = uu____8491;
               FStar_Ident.nsstr = uu____8492; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8512 =
              let uu____8513 =
                let uu____8514 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8514  in
              mk1 uu____8513  in
            (uu____8512, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8515; FStar_Ident.ident = uu____8516;
              FStar_Ident.nsstr = uu____8517; FStar_Ident.str = "Effect";_}
            ->
            let uu____8522 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8522, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8523; FStar_Ident.ident = uu____8524;
              FStar_Ident.nsstr = uu____8525; FStar_Ident.str = "True";_}
            ->
            let uu____8530 =
              let uu____8531 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8531
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8530, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8532; FStar_Ident.ident = uu____8533;
              FStar_Ident.nsstr = uu____8534; FStar_Ident.str = "False";_}
            ->
            let uu____8539 =
              let uu____8540 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8540
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8539, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8543;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8546 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8546 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8555 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8555, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8557 =
                    let uu____8559 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8559 txt
                     in
                  failwith uu____8557))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8568 = desugar_name mk1 setpos env true l  in
              (uu____8568, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8577 = desugar_name mk1 setpos env true l  in
              (uu____8577, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8595 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8595 with
                | FStar_Pervasives_Native.Some uu____8605 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8613 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8613 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8631 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8652 =
                    let uu____8653 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8653  in
                  (uu____8652, noaqs)
              | uu____8659 ->
                  let uu____8667 =
                    let uu____8673 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8673)  in
                  FStar_Errors.raise_error uu____8667
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8683 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8683 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8690 =
                    let uu____8696 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8696)
                     in
                  FStar_Errors.raise_error uu____8690
                    top.FStar_Parser_AST.range
              | uu____8704 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8708 = desugar_name mk1 setpos env true lid'  in
                  (uu____8708, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8730 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8730 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8749 ->
                       let uu____8756 =
                         FStar_Util.take
                           (fun uu____8780  ->
                              match uu____8780 with
                              | (uu____8786,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8756 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8831 =
                              let uu____8856 =
                                FStar_List.map
                                  (fun uu____8899  ->
                                     match uu____8899 with
                                     | (t,imp) ->
                                         let uu____8916 =
                                           desugar_term_aq env t  in
                                         (match uu____8916 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8856
                                FStar_List.unzip
                               in
                            (match uu____8831 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9059 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9059, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9078 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9078 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9089 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9117  ->
                 match uu___8_9117 with
                 | FStar_Util.Inr uu____9123 -> true
                 | uu____9125 -> false) binders
            ->
            let terms =
              let uu____9134 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9151  ->
                        match uu___9_9151 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9157 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9134 [t]  in
            let uu____9159 =
              let uu____9184 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9241 = desugar_typ_aq env t1  in
                        match uu____9241 with
                        | (t',aq) ->
                            let uu____9252 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9252, aq)))
                 in
              FStar_All.pipe_right uu____9184 FStar_List.unzip  in
            (match uu____9159 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9362 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9362
                    in
                 let uu____9371 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9371, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9398 =
              let uu____9415 =
                let uu____9422 =
                  let uu____9429 =
                    FStar_All.pipe_left (fun _9438  -> FStar_Util.Inl _9438)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9429]  in
                FStar_List.append binders uu____9422  in
              FStar_List.fold_left
                (fun uu____9483  ->
                   fun b  ->
                     match uu____9483 with
                     | (env1,tparams,typs) ->
                         let uu____9544 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9559 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9559)
                            in
                         (match uu____9544 with
                          | (xopt,t1) ->
                              let uu____9584 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9593 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9593)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9584 with
                               | (env2,x) ->
                                   let uu____9613 =
                                     let uu____9616 =
                                       let uu____9619 =
                                         let uu____9620 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9620
                                          in
                                       [uu____9619]  in
                                     FStar_List.append typs uu____9616  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1554_9646 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1554_9646.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1554_9646.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9613)))) (env, [], []) uu____9415
               in
            (match uu____9398 with
             | (env1,uu____9674,targs) ->
                 let tup =
                   let uu____9697 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9697
                    in
                 let uu____9698 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9698, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9717 = uncurry binders t  in
            (match uu____9717 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9761 =
                   match uu___10_9761 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9778 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9778
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9802 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9802 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9835 = aux env [] bs  in (uu____9835, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9844 = desugar_binder env b  in
            (match uu____9844 with
             | (FStar_Pervasives_Native.None ,uu____9855) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9870 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9870 with
                  | ((x,uu____9886),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9899 =
                        let uu____9900 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9900  in
                      (uu____9899, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9978 = FStar_Util.set_is_empty i  in
                    if uu____9978
                    then
                      let uu____9983 = FStar_Util.set_union acc set1  in
                      aux uu____9983 sets2
                    else
                      (let uu____9988 =
                         let uu____9989 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9989  in
                       FStar_Pervasives_Native.Some uu____9988)
                 in
              let uu____9992 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9992 sets  in
            ((let uu____9996 = check_disjoint bvss  in
              match uu____9996 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10000 =
                    let uu____10006 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10006)
                     in
                  let uu____10010 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10000 uu____10010);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10018 =
                FStar_List.fold_left
                  (fun uu____10038  ->
                     fun pat  ->
                       match uu____10038 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10064,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10074 =
                                  let uu____10077 = free_type_vars env1 t  in
                                  FStar_List.append uu____10077 ftvs  in
                                (env1, uu____10074)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10082,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10093 =
                                  let uu____10096 = free_type_vars env1 t  in
                                  let uu____10099 =
                                    let uu____10102 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10102 ftvs  in
                                  FStar_List.append uu____10096 uu____10099
                                   in
                                (env1, uu____10093)
                            | uu____10107 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10018 with
              | (uu____10116,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10128 =
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
                    FStar_List.append uu____10128 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10208 = desugar_term_aq env1 body  in
                        (match uu____10208 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10243 =
                                       let uu____10244 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10244
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10243
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
                             let uu____10313 =
                               let uu____10314 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10314  in
                             (uu____10313, aq))
                    | p::rest ->
                        let uu____10327 = desugar_binding_pat env1 p  in
                        (match uu____10327 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10359)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10374 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10383 =
                               match b with
                               | LetBinder uu____10424 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10493) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10547 =
                                           let uu____10556 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10556, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10547
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10618,uu____10619) ->
                                              let tup2 =
                                                let uu____10621 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10621
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10626 =
                                                  let uu____10633 =
                                                    let uu____10634 =
                                                      let uu____10651 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10654 =
                                                        let uu____10665 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10674 =
                                                          let uu____10685 =
                                                            let uu____10694 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10694
                                                             in
                                                          [uu____10685]  in
                                                        uu____10665 ::
                                                          uu____10674
                                                         in
                                                      (uu____10651,
                                                        uu____10654)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10634
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10633
                                                   in
                                                uu____10626
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10742 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10742
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10793,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10795,pats1)) ->
                                              let tupn =
                                                let uu____10840 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10840
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10853 =
                                                  let uu____10854 =
                                                    let uu____10871 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10874 =
                                                      let uu____10885 =
                                                        let uu____10896 =
                                                          let uu____10905 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10905
                                                           in
                                                        [uu____10896]  in
                                                      FStar_List.append args
                                                        uu____10885
                                                       in
                                                    (uu____10871,
                                                      uu____10874)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10854
                                                   in
                                                mk1 uu____10853  in
                                              let p2 =
                                                let uu____10953 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10953
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11000 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10383 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11092,uu____11093,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11115 =
                let uu____11116 = unparen e  in
                uu____11116.FStar_Parser_AST.tm  in
              match uu____11115 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11126 ->
                  let uu____11127 = desugar_term_aq env e  in
                  (match uu____11127 with
                   | (head1,aq) ->
                       let uu____11140 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11140, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11147 ->
            let rec aux args aqs e =
              let uu____11224 =
                let uu____11225 = unparen e  in
                uu____11225.FStar_Parser_AST.tm  in
              match uu____11224 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11243 = desugar_term_aq env t  in
                  (match uu____11243 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11291 ->
                  let uu____11292 = desugar_term_aq env e  in
                  (match uu____11292 with
                   | (head1,aq) ->
                       let uu____11313 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11313, (join_aqs (aq :: aqs))))
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
            let uu____11376 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11376
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
            let uu____11428 = desugar_term_aq env t  in
            (match uu____11428 with
             | (tm,s) ->
                 let uu____11439 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11439, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11445 =
              let uu____11458 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11458 then desugar_typ_aq else desugar_term_aq  in
            uu____11445 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11525 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11668  ->
                        match uu____11668 with
                        | (attr_opt,(p,def)) ->
                            let uu____11726 = is_app_pattern p  in
                            if uu____11726
                            then
                              let uu____11759 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11759, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11842 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11842, def1)
                               | uu____11887 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11925);
                                           FStar_Parser_AST.prange =
                                             uu____11926;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11975 =
                                            let uu____11996 =
                                              let uu____12001 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12001  in
                                            (uu____11996, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11975, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12093) ->
                                        if top_level
                                        then
                                          let uu____12129 =
                                            let uu____12150 =
                                              let uu____12155 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12155  in
                                            (uu____12150, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12129, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12246 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12279 =
                FStar_List.fold_left
                  (fun uu____12368  ->
                     fun uu____12369  ->
                       match (uu____12368, uu____12369) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12499,uu____12500),uu____12501))
                           ->
                           let uu____12635 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12675 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12675 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12710 =
                                        let uu____12713 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12713 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12710, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12729 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12729 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12635 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12279 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12982 =
                    match uu____12982 with
                    | (attrs_opt,(uu____13022,args,result_t),def) ->
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
                                let uu____13114 = is_comp_type env1 t  in
                                if uu____13114
                                then
                                  ((let uu____13118 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13128 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13128))
                                       in
                                    match uu____13118 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13135 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13138 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13138))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13135
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
                          | uu____13149 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13152 = desugar_term_aq env1 def2  in
                        (match uu____13152 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13174 =
                                     let uu____13175 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13175
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13174
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
                  let uu____13216 =
                    let uu____13233 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13233 FStar_List.unzip  in
                  (match uu____13216 with
                   | (lbs1,aqss) ->
                       let uu____13375 = desugar_term_aq env' body  in
                       (match uu____13375 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13481  ->
                                    fun used_marker  ->
                                      match uu____13481 with
                                      | (_attr_opt,(f,uu____13555,uu____13556),uu____13557)
                                          ->
                                          let uu____13614 =
                                            let uu____13616 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13616  in
                                          if uu____13614
                                          then
                                            let uu____13640 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13658 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13660 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13658, "Local",
                                                    uu____13660)
                                              | FStar_Util.Inr l ->
                                                  let uu____13665 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13667 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13665, "Global",
                                                    uu____13667)
                                               in
                                            (match uu____13640 with
                                             | (nm,gl,rng) ->
                                                 let uu____13678 =
                                                   let uu____13684 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13684)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13678)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13692 =
                                let uu____13695 =
                                  let uu____13696 =
                                    let uu____13710 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13710)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13696  in
                                FStar_All.pipe_left mk1 uu____13695  in
                              (uu____13692,
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
              let uu____13812 = desugar_term_aq env t1  in
              match uu____13812 with
              | (t11,aq0) ->
                  let uu____13833 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13833 with
                   | (env1,binder,pat1) ->
                       let uu____13863 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13905 = desugar_term_aq env1 t2  in
                             (match uu____13905 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13927 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13927
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13928 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13928, aq))
                         | LocalBinder (x,uu____13969) ->
                             let uu____13970 = desugar_term_aq env1 t2  in
                             (match uu____13970 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13992;
                                         FStar_Syntax_Syntax.p = uu____13993;_},uu____13994)::[]
                                        -> body1
                                    | uu____14007 ->
                                        let uu____14010 =
                                          let uu____14017 =
                                            let uu____14018 =
                                              let uu____14041 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14044 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14041, uu____14044)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14018
                                             in
                                          FStar_Syntax_Syntax.mk uu____14017
                                           in
                                        uu____14010
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14081 =
                                    let uu____14084 =
                                      let uu____14085 =
                                        let uu____14099 =
                                          let uu____14102 =
                                            let uu____14103 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14103]  in
                                          FStar_Syntax_Subst.close
                                            uu____14102 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14099)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14085
                                       in
                                    FStar_All.pipe_left mk1 uu____14084  in
                                  (uu____14081, aq))
                          in
                       (match uu____13863 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14211 = FStar_List.hd lbs  in
            (match uu____14211 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14255 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14255
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14271 =
                let uu____14272 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14272  in
              mk1 uu____14271  in
            let uu____14273 = desugar_term_aq env t1  in
            (match uu____14273 with
             | (t1',aq1) ->
                 let uu____14284 = desugar_term_aq env t2  in
                 (match uu____14284 with
                  | (t2',aq2) ->
                      let uu____14295 = desugar_term_aq env t3  in
                      (match uu____14295 with
                       | (t3',aq3) ->
                           let uu____14306 =
                             let uu____14307 =
                               let uu____14308 =
                                 let uu____14331 =
                                   let uu____14348 =
                                     let uu____14363 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14363,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14377 =
                                     let uu____14394 =
                                       let uu____14409 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14409,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14394]  in
                                   uu____14348 :: uu____14377  in
                                 (t1', uu____14331)  in
                               FStar_Syntax_Syntax.Tm_match uu____14308  in
                             mk1 uu____14307  in
                           (uu____14306, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14605 =
              match uu____14605 with
              | (pat,wopt,b) ->
                  let uu____14627 = desugar_match_pat env pat  in
                  (match uu____14627 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14658 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14658
                          in
                       let uu____14663 = desugar_term_aq env1 b  in
                       (match uu____14663 with
                        | (b1,aq) ->
                            let uu____14676 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14676, aq)))
               in
            let uu____14681 = desugar_term_aq env e  in
            (match uu____14681 with
             | (e1,aq) ->
                 let uu____14692 =
                   let uu____14723 =
                     let uu____14756 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14756 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14723
                     (fun uu____14974  ->
                        match uu____14974 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14692 with
                  | (brs,aqs) ->
                      let uu____15193 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15193, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15227 =
              let uu____15248 = is_comp_type env t  in
              if uu____15248
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15303 = desugar_term_aq env t  in
                 match uu____15303 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15227 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15395 = desugar_term_aq env e  in
                 (match uu____15395 with
                  | (e1,aq) ->
                      let uu____15406 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15406, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15445,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15488 = FStar_List.hd fields  in
              match uu____15488 with | (f,uu____15500) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15546  ->
                        match uu____15546 with
                        | (g,uu____15553) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15560,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15574 =
                         let uu____15580 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15580)
                          in
                       FStar_Errors.raise_error uu____15574
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
                  let uu____15591 =
                    let uu____15602 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15633  ->
                              match uu____15633 with
                              | (f,uu____15643) ->
                                  let uu____15644 =
                                    let uu____15645 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15645
                                     in
                                  (uu____15644, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15602)  in
                  FStar_Parser_AST.Construct uu____15591
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15663 =
                      let uu____15664 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15664  in
                    FStar_Parser_AST.mk_term uu____15663
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15666 =
                      let uu____15679 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15709  ->
                                match uu____15709 with
                                | (f,uu____15719) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15679)  in
                    FStar_Parser_AST.Record uu____15666  in
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
            let uu____15779 = desugar_term_aq env recterm1  in
            (match uu____15779 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15795;
                         FStar_Syntax_Syntax.vars = uu____15796;_},args)
                      ->
                      let uu____15822 =
                        let uu____15823 =
                          let uu____15824 =
                            let uu____15841 =
                              let uu____15844 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15845 =
                                let uu____15848 =
                                  let uu____15849 =
                                    let uu____15856 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15856)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15849
                                   in
                                FStar_Pervasives_Native.Some uu____15848  in
                              FStar_Syntax_Syntax.fvar uu____15844
                                FStar_Syntax_Syntax.delta_constant
                                uu____15845
                               in
                            (uu____15841, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15824  in
                        FStar_All.pipe_left mk1 uu____15823  in
                      (uu____15822, s)
                  | uu____15885 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15889 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15889 with
              | (constrname,is_rec) ->
                  let uu____15908 = desugar_term_aq env e  in
                  (match uu____15908 with
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
                       let uu____15928 =
                         let uu____15929 =
                           let uu____15930 =
                             let uu____15947 =
                               let uu____15950 =
                                 let uu____15951 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15951
                                  in
                               FStar_Syntax_Syntax.fvar uu____15950
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15953 =
                               let uu____15964 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15964]  in
                             (uu____15947, uu____15953)  in
                           FStar_Syntax_Syntax.Tm_app uu____15930  in
                         FStar_All.pipe_left mk1 uu____15929  in
                       (uu____15928, s))))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____16004 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____16004
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16015 =
              let uu____16016 = FStar_Syntax_Subst.compress tm  in
              uu____16016.FStar_Syntax_Syntax.n  in
            (match uu____16015 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16024 =
                   let uu___2123_16025 =
                     let uu____16026 =
                       let uu____16028 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16028  in
                     FStar_Syntax_Util.exp_string uu____16026  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2123_16025.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2123_16025.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16024, noaqs)
             | uu____16029 ->
                 let uu____16030 =
                   let uu____16036 =
                     let uu____16038 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16038
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16036)  in
                 FStar_Errors.raise_error uu____16030
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16047 = desugar_term_aq env e  in
            (match uu____16047 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16059 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16059, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16064 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16065 =
              let uu____16066 =
                let uu____16073 = desugar_term env e  in (bv, uu____16073)
                 in
              [uu____16066]  in
            (uu____16064, uu____16065)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16098 =
              let uu____16099 =
                let uu____16100 =
                  let uu____16107 = desugar_term env e  in (uu____16107, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16100  in
              FStar_All.pipe_left mk1 uu____16099  in
            (uu____16098, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16136 -> false  in
              let uu____16138 =
                let uu____16139 = unparen rel1  in
                uu____16139.FStar_Parser_AST.tm  in
              match uu____16138 with
              | FStar_Parser_AST.Op (id1,uu____16142) ->
                  let uu____16147 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16147 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16155 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16155 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16166 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16166 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16172 -> false  in
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
              let uu____16193 =
                let uu____16194 =
                  let uu____16201 =
                    let uu____16202 =
                      let uu____16203 =
                        let uu____16212 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16225 =
                          let uu____16226 =
                            let uu____16227 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16227  in
                          FStar_Parser_AST.mk_term uu____16226
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16212, uu____16225,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16203  in
                    FStar_Parser_AST.mk_term uu____16202
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16201)  in
                FStar_Parser_AST.Abs uu____16194  in
              FStar_Parser_AST.mk_term uu____16193
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
              let uu____16248 = FStar_List.last steps  in
              match uu____16248 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16251,uu____16252,last_expr)) -> last_expr
              | uu____16254 -> failwith "impossible: no last_expr on calc"
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
            let uu____16282 =
              FStar_List.fold_left
                (fun uu____16300  ->
                   fun uu____16301  ->
                     match (uu____16300, uu____16301) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16324 = is_impl rel2  in
                           if uu____16324
                           then
                             let uu____16327 =
                               let uu____16334 =
                                 let uu____16339 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16339, FStar_Parser_AST.Nothing)  in
                               [uu____16334]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16327 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16351 =
                             let uu____16358 =
                               let uu____16365 =
                                 let uu____16372 =
                                   let uu____16379 =
                                     let uu____16384 = eta_and_annot rel2  in
                                     (uu____16384, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16385 =
                                     let uu____16392 =
                                       let uu____16399 =
                                         let uu____16404 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16404,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16405 =
                                         let uu____16412 =
                                           let uu____16417 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16417,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16412]  in
                                       uu____16399 :: uu____16405  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16392
                                      in
                                   uu____16379 :: uu____16385  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16372
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16365
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16358
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16351
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16282 with
             | (e1,uu____16455) ->
                 let e2 =
                   let uu____16457 =
                     let uu____16464 =
                       let uu____16471 =
                         let uu____16478 =
                           let uu____16483 = FStar_Parser_AST.thunk e1  in
                           (uu____16483, FStar_Parser_AST.Nothing)  in
                         [uu____16478]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16471  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16464  in
                   FStar_Parser_AST.mkApp finish1 uu____16457
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16500 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16501 = desugar_formula env top  in
            (uu____16501, noaqs)
        | uu____16502 ->
            let uu____16503 =
              let uu____16509 =
                let uu____16511 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16511  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16509)  in
            FStar_Errors.raise_error uu____16503 top.FStar_Parser_AST.range

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
           (fun uu____16555  ->
              match uu____16555 with
              | (a,imp) ->
                  let uu____16568 = desugar_term env a  in
                  arg_withimp_e imp uu____16568))

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
          let is_requires uu____16605 =
            match uu____16605 with
            | (t1,uu____16612) ->
                let uu____16613 =
                  let uu____16614 = unparen t1  in
                  uu____16614.FStar_Parser_AST.tm  in
                (match uu____16613 with
                 | FStar_Parser_AST.Requires uu____16616 -> true
                 | uu____16625 -> false)
             in
          let is_ensures uu____16637 =
            match uu____16637 with
            | (t1,uu____16644) ->
                let uu____16645 =
                  let uu____16646 = unparen t1  in
                  uu____16646.FStar_Parser_AST.tm  in
                (match uu____16645 with
                 | FStar_Parser_AST.Ensures uu____16648 -> true
                 | uu____16657 -> false)
             in
          let is_app head1 uu____16675 =
            match uu____16675 with
            | (t1,uu____16683) ->
                let uu____16684 =
                  let uu____16685 = unparen t1  in
                  uu____16685.FStar_Parser_AST.tm  in
                (match uu____16684 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16688;
                        FStar_Parser_AST.level = uu____16689;_},uu____16690,uu____16691)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16693 -> false)
             in
          let is_smt_pat uu____16705 =
            match uu____16705 with
            | (t1,uu____16712) ->
                let uu____16713 =
                  let uu____16714 = unparen t1  in
                  uu____16714.FStar_Parser_AST.tm  in
                (match uu____16713 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16718);
                               FStar_Parser_AST.range = uu____16719;
                               FStar_Parser_AST.level = uu____16720;_},uu____16721)::uu____16722::[])
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
                               FStar_Parser_AST.range = uu____16771;
                               FStar_Parser_AST.level = uu____16772;_},uu____16773)::uu____16774::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16807 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16842 = head_and_args t1  in
            match uu____16842 with
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
                     let thunk_ens uu____16935 =
                       match uu____16935 with
                       | (e,i) ->
                           let uu____16946 = FStar_Parser_AST.thunk e  in
                           (uu____16946, i)
                        in
                     let fail_lemma uu____16958 =
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
                           let uu____17064 =
                             let uu____17071 =
                               let uu____17078 = thunk_ens ens  in
                               [uu____17078; nil_pat]  in
                             req_true :: uu____17071  in
                           unit_tm :: uu____17064
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17125 =
                             let uu____17132 =
                               let uu____17139 = thunk_ens ens  in
                               [uu____17139; nil_pat]  in
                             req :: uu____17132  in
                           unit_tm :: uu____17125
                       | ens::smtpat::[] when
                           (((let uu____17188 = is_requires ens  in
                              Prims.op_Negation uu____17188) &&
                               (let uu____17191 = is_smt_pat ens  in
                                Prims.op_Negation uu____17191))
                              &&
                              (let uu____17194 = is_decreases ens  in
                               Prims.op_Negation uu____17194))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17196 =
                             let uu____17203 =
                               let uu____17210 = thunk_ens ens  in
                               [uu____17210; smtpat]  in
                             req_true :: uu____17203  in
                           unit_tm :: uu____17196
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17257 =
                             let uu____17264 =
                               let uu____17271 = thunk_ens ens  in
                               [uu____17271; nil_pat; dec]  in
                             req_true :: uu____17264  in
                           unit_tm :: uu____17257
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17331 =
                             let uu____17338 =
                               let uu____17345 = thunk_ens ens  in
                               [uu____17345; smtpat; dec]  in
                             req_true :: uu____17338  in
                           unit_tm :: uu____17331
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17405 =
                             let uu____17412 =
                               let uu____17419 = thunk_ens ens  in
                               [uu____17419; nil_pat; dec]  in
                             req :: uu____17412  in
                           unit_tm :: uu____17405
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17479 =
                             let uu____17486 =
                               let uu____17493 = thunk_ens ens  in
                               [uu____17493; smtpat]  in
                             req :: uu____17486  in
                           unit_tm :: uu____17479
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17558 =
                             let uu____17565 =
                               let uu____17572 = thunk_ens ens  in
                               [uu____17572; dec; smtpat]  in
                             req :: uu____17565  in
                           unit_tm :: uu____17558
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17634 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17634, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17662 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17662
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17665 =
                       let uu____17672 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17672, [])  in
                     (uu____17665, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17690 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17690
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17693 =
                       let uu____17700 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17700, [])  in
                     (uu____17693, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17722 =
                       let uu____17729 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17729, [])  in
                     (uu____17722, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17752 when allow_type_promotion ->
                     let default_effect =
                       let uu____17754 = FStar_Options.ml_ish ()  in
                       if uu____17754
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17760 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17760
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17767 =
                       let uu____17774 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17774, [])  in
                     (uu____17767, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17797 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17816 = pre_process_comp_typ t  in
          match uu____17816 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17868 =
                    let uu____17874 =
                      let uu____17876 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17876
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17874)
                     in
                  fail1 uu____17868)
               else ();
               (let is_universe uu____17892 =
                  match uu____17892 with
                  | (uu____17898,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17900 = FStar_Util.take is_universe args  in
                match uu____17900 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17959  ->
                           match uu____17959 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17966 =
                      let uu____17981 = FStar_List.hd args1  in
                      let uu____17990 = FStar_List.tl args1  in
                      (uu____17981, uu____17990)  in
                    (match uu____17966 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18045 =
                           let is_decrease uu____18084 =
                             match uu____18084 with
                             | (t1,uu____18095) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18106;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18107;_},uu____18108::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18147 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18045 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18264  ->
                                        match uu____18264 with
                                        | (t1,uu____18274) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18283,(arg,uu____18285)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18324 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18345 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18357 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18357
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18364 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18364
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18374 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18374
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18381 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18381
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18388 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18388
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18395 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18395
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18416 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18416
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
                                                    let uu____18507 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18507
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
                                              | uu____18528 -> pat  in
                                            let uu____18529 =
                                              let uu____18540 =
                                                let uu____18551 =
                                                  let uu____18560 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18560, aq)  in
                                                [uu____18551]  in
                                              ens :: uu____18540  in
                                            req :: uu____18529
                                        | uu____18601 -> rest2
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
        let uu___2448_18636 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2448_18636.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2448_18636.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2455_18690 = b  in
             {
               FStar_Parser_AST.b = (uu___2455_18690.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2455_18690.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2455_18690.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18719 body1 =
          match uu____18719 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18765::uu____18766) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18784 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2474_18811 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2474_18811.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2474_18811.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18874 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18874))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18905 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18905 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2487_18915 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2487_18915.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2487_18915.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18921 =
                     let uu____18924 =
                       let uu____18925 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18925]  in
                     no_annot_abs uu____18924 body2  in
                   FStar_All.pipe_left setpos uu____18921  in
                 let uu____18946 =
                   let uu____18947 =
                     let uu____18964 =
                       let uu____18967 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18967
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18969 =
                       let uu____18980 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18980]  in
                     (uu____18964, uu____18969)  in
                   FStar_Syntax_Syntax.Tm_app uu____18947  in
                 FStar_All.pipe_left mk1 uu____18946)
        | uu____19019 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19084 = q (rest, pats, body)  in
              let uu____19087 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19084 uu____19087
                FStar_Parser_AST.Formula
               in
            let uu____19088 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19088 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19099 -> failwith "impossible"  in
      let uu____19103 =
        let uu____19104 = unparen f  in uu____19104.FStar_Parser_AST.tm  in
      match uu____19103 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19117,uu____19118) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19142,uu____19143) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19199 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19199
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19243 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19243
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19307 -> desugar_term env f

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
          let uu____19318 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19318)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19323 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19323)
      | FStar_Parser_AST.TVariable x ->
          let uu____19327 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19327)
      | FStar_Parser_AST.NoName t ->
          let uu____19331 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19331)
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
      fun uu___11_19339  ->
        match uu___11_19339 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19361 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19361, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19378 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19378 with
             | (env1,a1) ->
                 let uu____19395 =
                   let uu____19402 = trans_aqual env1 imp  in
                   ((let uu___2587_19408 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2587_19408.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2587_19408.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19402)
                    in
                 (uu____19395, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19416  ->
      match uu___12_19416 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19420 =
            let uu____19421 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19421  in
          FStar_Pervasives_Native.Some uu____19420
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19449 =
        FStar_List.fold_left
          (fun uu____19482  ->
             fun b  ->
               match uu____19482 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2605_19526 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2605_19526.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2605_19526.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2605_19526.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19541 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19541 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2615_19559 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2615_19559.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2615_19559.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19560 =
                               let uu____19567 =
                                 let uu____19572 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19572)  in
                               uu____19567 :: out  in
                             (env2, uu____19560))
                    | uu____19583 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19449 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19671 =
          let uu____19672 = unparen t  in uu____19672.FStar_Parser_AST.tm  in
        match uu____19671 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19673; FStar_Ident.ident = uu____19674;
              FStar_Ident.nsstr = uu____19675; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19680 ->
            let uu____19681 =
              let uu____19687 =
                let uu____19689 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19689  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19687)  in
            FStar_Errors.raise_error uu____19681 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19706) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19708) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19711 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19729 = binder_ident b  in
         FStar_Common.list_of_option uu____19729) bs
  
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
               (fun uu___13_19766  ->
                  match uu___13_19766 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19771 -> false))
           in
        let quals2 q =
          let uu____19785 =
            (let uu____19789 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19789) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19785
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19806 = FStar_Ident.range_of_lid disc_name  in
                let uu____19807 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19806;
                  FStar_Syntax_Syntax.sigquals = uu____19807;
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
            let uu____19847 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19885  ->
                        match uu____19885 with
                        | (x,uu____19896) ->
                            let uu____19901 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19901 with
                             | (field_name,uu____19909) ->
                                 let only_decl =
                                   ((let uu____19914 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19914)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19916 =
                                        let uu____19918 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19918.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19916)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19936 =
                                       FStar_List.filter
                                         (fun uu___14_19940  ->
                                            match uu___14_19940 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19943 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19936
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19958  ->
                                             match uu___15_19958 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19963 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19966 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19966;
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
                                      let uu____19973 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19973
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19984 =
                                        let uu____19989 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19989  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19984;
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
                                      let uu____19993 =
                                        let uu____19994 =
                                          let uu____20001 =
                                            let uu____20004 =
                                              let uu____20005 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____20005
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____20004]  in
                                          ((false, [lb]), uu____20001)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19994
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19993;
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
            FStar_All.pipe_right uu____19847 FStar_List.flatten
  
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
            (lid,uu____20054,t,uu____20056,n1,uu____20058) when
            let uu____20065 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20065 ->
            let uu____20067 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20067 with
             | (formals,uu____20085) ->
                 (match formals with
                  | [] -> []
                  | uu____20114 ->
                      let filter_records uu___16_20130 =
                        match uu___16_20130 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20133,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20145 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20147 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20147 with
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
                      let uu____20159 = FStar_Util.first_N n1 formals  in
                      (match uu____20159 with
                       | (uu____20188,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20222 -> []
  
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
                        let uu____20316 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20316
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20340 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20340
                        then
                          let uu____20346 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20346
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20350 =
                          let uu____20355 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20355  in
                        let uu____20356 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20362 =
                              let uu____20365 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20365  in
                            FStar_Syntax_Util.arrow typars uu____20362
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20370 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20350;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20356;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20370;
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
          let tycon_id uu___17_20424 =
            match uu___17_20424 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20426,uu____20427) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20437,uu____20438,uu____20439) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20449,uu____20450,uu____20451) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20473,uu____20474,uu____20475) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20513) ->
                let uu____20514 =
                  let uu____20515 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20515  in
                FStar_Parser_AST.mk_term uu____20514 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20517 =
                  let uu____20518 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20518  in
                FStar_Parser_AST.mk_term uu____20517 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20520) ->
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
              | uu____20551 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20559 =
                     let uu____20560 =
                       let uu____20567 = binder_to_term1 b  in
                       (out, uu____20567, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20560  in
                   FStar_Parser_AST.mk_term uu____20559
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20579 =
            match uu___18_20579 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20623  ->
                       match uu____20623 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20631 =
                    let uu____20632 =
                      let uu____20633 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20633  in
                    FStar_Parser_AST.mk_term uu____20632
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20631 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20640 = binder_idents parms  in id1 ::
                    uu____20640
                   in
                (FStar_List.iter
                   (fun uu____20653  ->
                      match uu____20653 with
                      | (f,uu____20659) ->
                          let uu____20660 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20660
                          then
                            let uu____20665 =
                              let uu____20671 =
                                let uu____20673 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20673
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20671)
                               in
                            FStar_Errors.raise_error uu____20665
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20679 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20679)))
            | uu____20733 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20773 =
            match uu___19_20773 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20797 = typars_of_binders _env binders  in
                (match uu____20797 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20833 =
                         let uu____20834 =
                           let uu____20835 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20835  in
                         FStar_Parser_AST.mk_term uu____20834
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20833 binders  in
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
                     let uu____20844 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20844 with
                      | (_env1,uu____20861) ->
                          let uu____20868 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20868 with
                           | (_env2,uu____20885) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20892 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20935 =
              FStar_List.fold_left
                (fun uu____20969  ->
                   fun uu____20970  ->
                     match (uu____20969, uu____20970) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21039 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21039 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20935 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21130 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21130
                | uu____21131 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21139 = desugar_abstract_tc quals env [] tc  in
              (match uu____21139 with
               | (uu____21152,uu____21153,se,uu____21155) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21158,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21177 =
                                 let uu____21179 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21179  in
                               if uu____21177
                               then
                                 let uu____21182 =
                                   let uu____21188 =
                                     let uu____21190 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21190
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21188)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21182
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
                           | uu____21203 ->
                               let uu____21204 =
                                 let uu____21211 =
                                   let uu____21212 =
                                     let uu____21227 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21227)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21212
                                    in
                                 FStar_Syntax_Syntax.mk uu____21211  in
                               uu____21204 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2898_21240 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2898_21240.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2898_21240.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2898_21240.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2898_21240.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21241 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21256 = typars_of_binders env binders  in
              (match uu____21256 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21290 =
                           FStar_Util.for_some
                             (fun uu___20_21293  ->
                                match uu___20_21293 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21296 -> false) quals
                            in
                         if uu____21290
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21304 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21304
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21309 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21315  ->
                               match uu___21_21315 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21318 -> false))
                        in
                     if uu____21309
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21332 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21332
                     then
                       let uu____21338 =
                         let uu____21345 =
                           let uu____21346 = unparen t  in
                           uu____21346.FStar_Parser_AST.tm  in
                         match uu____21345 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21367 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21397)::args_rev ->
                                   let uu____21409 =
                                     let uu____21410 = unparen last_arg  in
                                     uu____21410.FStar_Parser_AST.tm  in
                                   (match uu____21409 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21438 -> ([], args))
                               | uu____21447 -> ([], args)  in
                             (match uu____21367 with
                              | (cattributes,args1) ->
                                  let uu____21486 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21486))
                         | uu____21497 -> (t, [])  in
                       match uu____21338 with
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
                                  (fun uu___22_21520  ->
                                     match uu___22_21520 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21523 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21531)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21551 = tycon_record_as_variant trec  in
              (match uu____21551 with
               | (t,fs) ->
                   let uu____21568 =
                     let uu____21571 =
                       let uu____21572 =
                         let uu____21581 =
                           let uu____21584 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21584  in
                         (uu____21581, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21572  in
                     uu____21571 :: quals  in
                   desugar_tycon env d uu____21568 [t])
          | uu____21589::uu____21590 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21748 = et  in
                match uu____21748 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21958 ->
                         let trec = tc  in
                         let uu____21978 = tycon_record_as_variant trec  in
                         (match uu____21978 with
                          | (t,fs) ->
                              let uu____22034 =
                                let uu____22037 =
                                  let uu____22038 =
                                    let uu____22047 =
                                      let uu____22050 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22050  in
                                    (uu____22047, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22038
                                   in
                                uu____22037 :: quals1  in
                              collect_tcs uu____22034 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22128 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22128 with
                          | (env2,uu____22185,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22322 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22322 with
                          | (env2,uu____22379,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22495 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22541 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22541 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22993  ->
                             match uu___24_22993 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23047,uu____23048);
                                    FStar_Syntax_Syntax.sigrng = uu____23049;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23050;
                                    FStar_Syntax_Syntax.sigmeta = uu____23051;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23052;
                                    FStar_Syntax_Syntax.sigopts = uu____23053;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23115 =
                                     typars_of_binders env1 binders  in
                                   match uu____23115 with
                                   | (env2,tpars1) ->
                                       let uu____23142 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23142 with
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
                                 let uu____23171 =
                                   let uu____23182 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23182)  in
                                 [uu____23171]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23218);
                                    FStar_Syntax_Syntax.sigrng = uu____23219;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23221;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23222;
                                    FStar_Syntax_Syntax.sigopts = uu____23223;_},constrs,tconstr,quals1)
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
                                 let uu____23314 = push_tparams env1 tpars
                                    in
                                 (match uu____23314 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23373  ->
                                             match uu____23373 with
                                             | (x,uu____23385) ->
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
                                        let uu____23396 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23396
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23419 =
                                        let uu____23438 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23515  ->
                                                  match uu____23515 with
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
                                                        let uu____23558 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23558
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
                                                                uu___23_23569
                                                                 ->
                                                                match uu___23_23569
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23581
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23589 =
                                                        let uu____23600 =
                                                          let uu____23601 =
                                                            let uu____23602 =
                                                              let uu____23618
                                                                =
                                                                let uu____23619
                                                                  =
                                                                  let uu____23622
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23622
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23619
                                                                 in
                                                              (name, univs1,
                                                                uu____23618,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23602
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23601;
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
                                                        (tps, uu____23600)
                                                         in
                                                      (name, uu____23589)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23438
                                         in
                                      (match uu____23419 with
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
                             | uu____23754 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23835  ->
                             match uu____23835 with | (uu____23846,se) -> se))
                      in
                   let uu____23860 =
                     let uu____23867 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23867 rng
                      in
                   (match uu____23860 with
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
                               (fun uu____23912  ->
                                  match uu____23912 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23960,tps,k,uu____23963,constrs)
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
                                      let uu____23984 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23999 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24016,uu____24017,uu____24018,uu____24019,uu____24020)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24027
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23999
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24031 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24038  ->
                                                          match uu___25_24038
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24040 ->
                                                              true
                                                          | uu____24050 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24031))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23984
                                  | uu____24052 -> []))
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
      let uu____24089 =
        FStar_List.fold_left
          (fun uu____24124  ->
             fun b  ->
               match uu____24124 with
               | (env1,binders1) ->
                   let uu____24168 = desugar_binder env1 b  in
                   (match uu____24168 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24191 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24191 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24244 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24089 with
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
          let uu____24348 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24355  ->
                    match uu___26_24355 with
                    | FStar_Syntax_Syntax.Reflectable uu____24357 -> true
                    | uu____24359 -> false))
             in
          if uu____24348
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24364 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24364
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
        let warn1 uu____24415 =
          if warn
          then
            let uu____24417 =
              let uu____24423 =
                let uu____24425 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24425
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24423)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24417
          else ()  in
        let uu____24431 = FStar_Syntax_Util.head_and_args at  in
        match uu____24431 with
        | (hd1,args) ->
            let uu____24484 =
              let uu____24485 = FStar_Syntax_Subst.compress hd1  in
              uu____24485.FStar_Syntax_Syntax.n  in
            (match uu____24484 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24529)::[] ->
                      let uu____24554 =
                        let uu____24559 =
                          let uu____24568 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24568 a1  in
                        uu____24559 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24554 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24591 =
                             let uu____24597 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24597  in
                           (uu____24591, true)
                       | uu____24612 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24628 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24650 -> (FStar_Pervasives_Native.None, false))
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____24677 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____24677 with
        | FStar_Pervasives_Native.None  ->
            let uu____24680 =
              let uu____24686 =
                let uu____24688 =
                  let uu____24690 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____24690 " not found"  in
                Prims.op_Hat "Effect name " uu____24688  in
              (FStar_Errors.Fatal_EffectNotFound, uu____24686)  in
            FStar_Errors.raise_error uu____24680 r
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
                    let uu____24846 = desugar_binders monad_env eff_binders
                       in
                    match uu____24846 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____24885 =
                            let uu____24894 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24894  in
                          FStar_List.length uu____24885  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____24928 =
                              let uu____24934 =
                                let uu____24936 =
                                  let uu____24938 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____24938
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____24936  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____24934)
                               in
                            FStar_Errors.raise_error uu____24928
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
                                (uu____25006,uu____25007,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25009,uu____25010,uu____25011))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25026 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25029 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25041 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25041 mandatory_members)
                              eff_decls
                             in
                          match uu____25029 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25060 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25089  ->
                                        fun decl  ->
                                          match uu____25089 with
                                          | (env2,out) ->
                                              let uu____25109 =
                                                desugar_decl env2 decl  in
                                              (match uu____25109 with
                                               | (env3,ses) ->
                                                   let uu____25122 =
                                                     let uu____25125 =
                                                       FStar_List.hd ses  in
                                                     uu____25125 :: out  in
                                                   (env3, uu____25122)))
                                     (env1, []))
                                 in
                              (match uu____25060 with
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
                                                 (uu____25171,uu____25172,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25175,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25176,(def,uu____25178)::
                                                        (cps_type,uu____25180)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25181;
                                                     FStar_Parser_AST.level =
                                                       uu____25182;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25215 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25215 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25247 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25248 =
                                                        let uu____25249 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25249
                                                         in
                                                      let uu____25256 =
                                                        let uu____25257 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25257
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25247;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25248;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25256
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25264,uu____25265,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25268,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25284 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25284 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25316 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25317 =
                                                        let uu____25318 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25318
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25316;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25317;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25325 ->
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
                                       let uu____25344 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25344
                                        in
                                     let uu____25346 =
                                       let uu____25347 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25347
                                        in
                                     ([], uu____25346)  in
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
                                       let uu____25369 =
                                         let uu____25370 =
                                           let uu____25373 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25373
                                            in
                                         let uu____25375 =
                                           let uu____25378 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25378
                                            in
                                         let uu____25380 =
                                           let uu____25383 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25383
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
                                             uu____25370;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25375;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25380
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25369
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25417 =
                                            match uu____25417 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25464 =
                                            let uu____25465 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25467 =
                                              let uu____25472 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25472 to_comb
                                               in
                                            let uu____25490 =
                                              let uu____25495 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____25495 to_comb
                                               in
                                            let uu____25513 =
                                              let uu____25518 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____25518 to_comb
                                               in
                                            let uu____25536 =
                                              let uu____25541 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____25541 to_comb
                                               in
                                            let uu____25559 =
                                              let uu____25564 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____25564 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25465;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25467;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____25490;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____25513;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____25536;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____25559
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25464)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_25587  ->
                                                 match uu___27_25587 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____25590 -> true
                                                 | uu____25592 -> false)
                                              qualifiers
                                             in
                                          let uu____25594 =
                                            let uu____25595 =
                                              lookup1 "return_wp"  in
                                            let uu____25597 =
                                              lookup1 "bind_wp"  in
                                            let uu____25599 =
                                              lookup1 "stronger"  in
                                            let uu____25601 =
                                              lookup1 "if_then_else"  in
                                            let uu____25603 =
                                              lookup1 "ite_wp"  in
                                            let uu____25605 =
                                              lookup1 "close_wp"  in
                                            let uu____25607 =
                                              lookup1 "trivial"  in
                                            let uu____25609 =
                                              if rr
                                              then
                                                let uu____25615 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25615
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25619 =
                                              if rr
                                              then
                                                let uu____25625 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25625
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25629 =
                                              if rr
                                              then
                                                let uu____25635 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25635
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____25595;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____25597;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____25599;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____25601;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____25603;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____25605;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____25607;
                                              FStar_Syntax_Syntax.repr =
                                                uu____25609;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____25619;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____25629
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____25594)
                                      in
                                   let sigel =
                                     let uu____25640 =
                                       let uu____25641 =
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
                                           uu____25641
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____25640
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
                                               let uu____25658 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____25658) env3)
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
                let uu____25681 = desugar_binders env1 eff_binders  in
                match uu____25681 with
                | (env2,binders) ->
                    let uu____25718 =
                      let uu____25729 = head_and_args defn  in
                      match uu____25729 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25766 ->
                                let uu____25767 =
                                  let uu____25773 =
                                    let uu____25775 =
                                      let uu____25777 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25777 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25775  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25773)
                                   in
                                FStar_Errors.raise_error uu____25767
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25783 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25813)::args_rev ->
                                let uu____25825 =
                                  let uu____25826 = unparen last_arg  in
                                  uu____25826.FStar_Parser_AST.tm  in
                                (match uu____25825 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25854 -> ([], args))
                            | uu____25863 -> ([], args)  in
                          (match uu____25783 with
                           | (cattributes,args1) ->
                               let uu____25906 = desugar_args env2 args1  in
                               let uu____25907 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25906, uu____25907))
                       in
                    (match uu____25718 with
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
                          (let uu____25947 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25947 with
                           | (ed_binders,uu____25961,ed_binders_opening) ->
                               let sub' shift_n uu____25980 =
                                 match uu____25980 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25995 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25995 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25999 =
                                       let uu____26000 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26000)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25999
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26021 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26022 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26023 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26039 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26040 =
                                          let uu____26041 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26041
                                           in
                                        let uu____26056 =
                                          let uu____26057 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26057
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26039;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26040;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26056
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
                                     uu____26021;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26022;
                                   FStar_Syntax_Syntax.actions = uu____26023;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26073 =
                                   let uu____26076 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26076 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26073;
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
                                           let uu____26091 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26091) env3)
                                  in
                               let env5 =
                                 let uu____26093 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26093
                                 then
                                   let reflect_lid =
                                     let uu____26100 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26100
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
        let uu____26117 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26117 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26132 = desugar_decl_noattrs env d  in
      match uu____26132 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26157;
                FStar_Syntax_Syntax.sigrng = uu____26158;
                FStar_Syntax_Syntax.sigquals = uu____26159;
                FStar_Syntax_Syntax.sigmeta = uu____26160;
                FStar_Syntax_Syntax.sigattrs = uu____26161;
                FStar_Syntax_Syntax.sigopts = uu____26162;_}::[] ->
                let uu____26175 =
                  let uu____26178 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26178  in
                FStar_All.pipe_right uu____26175
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26186 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26186))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____26199;
                FStar_Syntax_Syntax.sigrng = uu____26200;
                FStar_Syntax_Syntax.sigquals = uu____26201;
                FStar_Syntax_Syntax.sigmeta = uu____26202;
                FStar_Syntax_Syntax.sigattrs = uu____26203;
                FStar_Syntax_Syntax.sigopts = uu____26204;_}::uu____26205 ->
                let uu____26230 =
                  let uu____26233 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26233  in
                FStar_All.pipe_right uu____26230
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26241 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26241))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____26257;
                FStar_Syntax_Syntax.sigquals = uu____26258;
                FStar_Syntax_Syntax.sigmeta = uu____26259;
                FStar_Syntax_Syntax.sigattrs = uu____26260;
                FStar_Syntax_Syntax.sigopts = uu____26261;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____26282 -> []  in
          let attrs1 =
            let uu____26288 = val_attrs sigelts  in
            FStar_List.append attrs uu____26288  in
          let uu____26291 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3445_26295 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3445_26295.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3445_26295.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3445_26295.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3445_26295.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3445_26295.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____26291)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26302 = desugar_decl_aux env d  in
      match uu____26302 with
      | (env1,ses) ->
          let uu____26313 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26313)

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
          let uu____26345 = FStar_Syntax_DsEnv.iface env  in
          if uu____26345
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26360 =
               let uu____26362 =
                 let uu____26364 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26365 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26364
                   uu____26365
                  in
               Prims.op_Negation uu____26362  in
             if uu____26360
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26379 =
                  let uu____26381 =
                    let uu____26383 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26383 lid  in
                  Prims.op_Negation uu____26381  in
                if uu____26379
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26397 =
                     let uu____26399 =
                       let uu____26401 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26401
                         lid
                        in
                     Prims.op_Negation uu____26399  in
                   if uu____26397
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26419 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26419, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26448)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26467 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____26476 =
            let uu____26481 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26481 tcs  in
          (match uu____26476 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26498 =
                   let uu____26499 =
                     let uu____26506 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26506  in
                   [uu____26499]  in
                 let uu____26519 =
                   let uu____26522 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26525 =
                     let uu____26536 =
                       let uu____26545 =
                         let uu____26546 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26546  in
                       FStar_Syntax_Syntax.as_arg uu____26545  in
                     [uu____26536]  in
                   FStar_Syntax_Util.mk_app uu____26522 uu____26525  in
                 FStar_Syntax_Util.abs uu____26498 uu____26519
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26586,id1))::uu____26588 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26591::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26595 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26595 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26601 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26601]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26622) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26632,uu____26633,uu____26634,uu____26635,uu____26636)
                     ->
                     let uu____26645 =
                       let uu____26646 =
                         let uu____26647 =
                           let uu____26654 = mkclass lid  in
                           (meths, uu____26654)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26647  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26646;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____26645]
                 | uu____26657 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26691;
                    FStar_Parser_AST.prange = uu____26692;_},uu____26693)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26703;
                    FStar_Parser_AST.prange = uu____26704;_},uu____26705)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26721;
                         FStar_Parser_AST.prange = uu____26722;_},uu____26723);
                    FStar_Parser_AST.prange = uu____26724;_},uu____26725)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26747;
                         FStar_Parser_AST.prange = uu____26748;_},uu____26749);
                    FStar_Parser_AST.prange = uu____26750;_},uu____26751)::[]
                   -> false
               | (p,uu____26780)::[] ->
                   let uu____26789 = is_app_pattern p  in
                   Prims.op_Negation uu____26789
               | uu____26791 -> false)
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
            let uu____26866 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26866 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26879 =
                     let uu____26880 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26880.FStar_Syntax_Syntax.n  in
                   match uu____26879 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26890) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____26921 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____26946  ->
                                match uu____26946 with
                                | (qs,ats) ->
                                    let uu____26973 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____26973 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____26921 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27027::uu____27028 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27031 -> val_quals  in
                            let quals2 =
                              let uu____27035 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27068  ->
                                        match uu____27068 with
                                        | (uu____27082,(uu____27083,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27035
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27103 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27103
                              then
                                let uu____27109 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3622_27124 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3624_27126 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3624_27126.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3624_27126.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3622_27124.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27109)
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
                   | uu____27151 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27159 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27178 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27159 with
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
                       let uu___3647_27215 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3647_27215.FStar_Parser_AST.prange)
                       }
                   | uu____27222 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3651_27229 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3651_27229.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3651_27229.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____27245 =
                     let uu____27246 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____27246  in
                   FStar_Parser_AST.mk_term uu____27245
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____27270 id_opt =
                   match uu____27270 with
                   | (env1,ses) ->
                       let uu____27292 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____27304 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____27304
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____27306 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27306
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
                               let uu____27312 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27312
                                in
                             let bv_pat1 =
                               let uu____27316 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____27316
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____27292 with
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
                            let uu____27377 = desugar_decl env1 id_decl  in
                            (match uu____27377 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____27413 id1 =
                   match uu____27413 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____27452 =
                   match uu____27452 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____27476 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____27476 FStar_Util.set_elements
                    in
                 let uu____27483 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____27486 = is_var_pattern pat  in
                      Prims.op_Negation uu____27486)
                    in
                 if uu____27483
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
            let uu____27510 = close_fun env t  in
            desugar_term env uu____27510  in
          let quals1 =
            let uu____27514 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27514
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27526 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27526;
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
                let uu____27539 =
                  let uu____27548 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27548]  in
                let uu____27567 =
                  let uu____27570 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27570
                   in
                FStar_Syntax_Util.arrow uu____27539 uu____27567
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
          let uu____27636 =
            let uu____27638 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____27638  in
          if uu____27636
          then
            let uu____27645 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____27663 =
                    let uu____27666 =
                      let uu____27667 = desugar_term env t  in
                      ([], uu____27667)  in
                    FStar_Pervasives_Native.Some uu____27666  in
                  (uu____27663, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____27680 =
                    let uu____27683 =
                      let uu____27684 = desugar_term env wp  in
                      ([], uu____27684)  in
                    FStar_Pervasives_Native.Some uu____27683  in
                  let uu____27691 =
                    let uu____27694 =
                      let uu____27695 = desugar_term env t  in
                      ([], uu____27695)  in
                    FStar_Pervasives_Native.Some uu____27694  in
                  (uu____27680, uu____27691)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____27707 =
                    let uu____27710 =
                      let uu____27711 = desugar_term env t  in
                      ([], uu____27711)  in
                    FStar_Pervasives_Native.Some uu____27710  in
                  (FStar_Pervasives_Native.None, uu____27707)
               in
            (match uu____27645 with
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
                   let uu____27745 =
                     let uu____27748 =
                       let uu____27749 = desugar_term env t  in
                       ([], uu____27749)  in
                     FStar_Pervasives_Native.Some uu____27748  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____27745
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
             | uu____27756 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____27769 =
            let uu____27770 =
              let uu____27771 =
                let uu____27772 =
                  let uu____27783 =
                    let uu____27784 = desugar_term env bind1  in
                    ([], uu____27784)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____27783,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____27772  in
              {
                FStar_Syntax_Syntax.sigel = uu____27771;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____27770]  in
          (env, uu____27769)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27803 =
              let uu____27804 =
                let uu____27811 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27811, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27804  in
            {
              FStar_Syntax_Syntax.sigel = uu____27803;
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
            let uu____27829 = FStar_Syntax_DsEnv.snapshot env  in
            FStar_All.pipe_right uu____27829 FStar_Pervasives_Native.snd  in
          let uu____27841 =
            FStar_Errors.catch_errors
              (fun uu____27859  ->
                 FStar_Options.with_saved_options
                   (fun uu____27865  -> desugar_decl_noattrs env d1))
             in
          (match uu____27841 with
           | (errs,r) ->
               (match (errs, r) with
                | ([],FStar_Pervasives_Native.Some (uu____27900,ses)) ->
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
                | (errs1,uu____27922) ->
                    if expected_errs = []
                    then (env0, [])
                    else
                      (let actual_errs =
                         FStar_List.concatMap
                           (fun i  ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs1
                          in
                       let uu____27958 =
                         FStar_Errors.find_multiset_discrepancy expected_errs
                           actual_errs
                          in
                       match uu____27958 with
                       | FStar_Pervasives_Native.None  -> (env0, [])
                       | FStar_Pervasives_Native.Some (e,n1,n2) ->
                           (FStar_List.iter FStar_Errors.print_issue errs1;
                            (let uu____28003 =
                               let uu____28009 =
                                 let uu____28011 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int expected_errs
                                    in
                                 let uu____28014 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int actual_errs
                                    in
                                 let uu____28017 = FStar_Util.string_of_int e
                                    in
                                 let uu____28019 =
                                   FStar_Util.string_of_int n2  in
                                 let uu____28021 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format5
                                   "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                   uu____28011 uu____28014 uu____28017
                                   uu____28019 uu____28021
                                  in
                               (FStar_Errors.Error_DidNotFail, uu____28009)
                                in
                             FStar_Errors.log_issue
                               d1.FStar_Parser_AST.drange uu____28003);
                            (env0, [])))))

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____28046 =
        FStar_List.fold_left
          (fun uu____28066  ->
             fun d  ->
               match uu____28066 with
               | (env1,sigelts) ->
                   let uu____28086 = desugar_decl env1 d  in
                   (match uu____28086 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28046 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28177) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28181;
               FStar_Syntax_Syntax.exports = uu____28182;
               FStar_Syntax_Syntax.is_interface = uu____28183;_},FStar_Parser_AST.Module
             (current_lid,uu____28185)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28194) ->
              let uu____28197 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28197
           in
        let uu____28202 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28244 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28244, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28266 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28266, mname, decls, false)
           in
        match uu____28202 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28308 = desugar_decls env2 decls  in
            (match uu____28308 with
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
          let uu____28376 =
            (FStar_Options.interactive ()) &&
              (let uu____28379 =
                 let uu____28381 =
                   let uu____28383 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28383  in
                 FStar_Util.get_file_extension uu____28381  in
               FStar_List.mem uu____28379 ["fsti"; "fsi"])
             in
          if uu____28376 then as_interface m else m  in
        let uu____28397 = desugar_modul_common curmod env m1  in
        match uu____28397 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28419 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28419, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28441 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28441 with
      | (env1,modul,pop_when_done) ->
          let uu____28458 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28458 with
           | (env2,modul1) ->
               ((let uu____28470 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28470
                 then
                   let uu____28473 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28473
                 else ());
                (let uu____28478 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28478, modul1))))
  
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
        (fun uu____28528  ->
           let uu____28529 = desugar_modul env modul  in
           match uu____28529 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28567  ->
           let uu____28568 = desugar_decls env decls  in
           match uu____28568 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28619  ->
             let uu____28620 = desugar_partial_modul modul env a_modul  in
             match uu____28620 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28715 ->
                  let t =
                    let uu____28725 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28725  in
                  let uu____28738 =
                    let uu____28739 = FStar_Syntax_Subst.compress t  in
                    uu____28739.FStar_Syntax_Syntax.n  in
                  (match uu____28738 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28751,uu____28752)
                       -> bs1
                   | uu____28777 -> failwith "Impossible")
               in
            let uu____28787 =
              let uu____28794 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28794
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28787 with
            | (binders,uu____28796,binders_opening) ->
                let erase_term t =
                  let uu____28804 =
                    let uu____28805 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28805  in
                  FStar_Syntax_Subst.close binders uu____28804  in
                let erase_tscheme uu____28823 =
                  match uu____28823 with
                  | (us,t) ->
                      let t1 =
                        let uu____28843 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28843 t  in
                      let uu____28846 =
                        let uu____28847 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28847  in
                      ([], uu____28846)
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
                    | uu____28870 ->
                        let bs =
                          let uu____28880 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28880  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28920 =
                          let uu____28921 =
                            let uu____28924 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28924  in
                          uu____28921.FStar_Syntax_Syntax.n  in
                        (match uu____28920 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28926,uu____28927) -> bs1
                         | uu____28952 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28960 =
                      let uu____28961 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28961  in
                    FStar_Syntax_Subst.close binders uu____28960  in
                  let uu___3976_28962 = action  in
                  let uu____28963 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28964 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3976_28962.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3976_28962.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28963;
                    FStar_Syntax_Syntax.action_typ = uu____28964
                  }  in
                let uu___3978_28965 = ed  in
                let uu____28966 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28967 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28968 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____28969 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3978_28965.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3978_28965.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28966;
                  FStar_Syntax_Syntax.signature = uu____28967;
                  FStar_Syntax_Syntax.combinators = uu____28968;
                  FStar_Syntax_Syntax.actions = uu____28969;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3978_28965.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3985_28985 = se  in
                  let uu____28986 =
                    let uu____28987 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28987  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28986;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3985_28985.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3985_28985.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3985_28985.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3985_28985.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3985_28985.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28989 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28990 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28990 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29007 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____29007
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29009 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29009)
  