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
  'uuuuuu659 .
    'uuuuuu659 ->
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
  'uuuuuu738 .
    env_t ->
      Prims.int ->
        'uuuuuu738 ->
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
  'uuuuuu4154 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4154) Prims.list ->
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
          FStar_All.pipe_right uu____4389 (fun uu____4394  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4418 =
              let uu____4420 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4420  in
            if uu____4418
            then ()
            else
              (let nonlinear_vars =
                 let uu____4429 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4429  in
               let first_nonlinear_var =
                 let uu____4433 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4433  in
               let uu____4436 =
                 let uu____4442 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4442)  in
               FStar_Errors.raise_error uu____4436 r)
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
          let uu____4769 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4769 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4786 ->
              let uu____4789 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4789 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4930 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4952 =
                  let uu____4958 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4958, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4952  in
              let p2 =
                let uu___934_4963 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_4963.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4980 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4983 = aux loc env1 p2  in
                match uu____4983 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5039 =
                      match binder with
                      | LetBinder uu____5060 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5085 = close_fun env1 t  in
                            desugar_term env1 uu____5085  in
                          let x1 =
                            let uu___960_5087 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5087.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5087.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5039 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5133 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5134 -> ()
                           | uu____5135 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5136 ->
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
              let uu____5154 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5154, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5167 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5167, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5185 = resolvex loc env1 x  in
              (match uu____5185 with
               | (loc1,env2,xbv) ->
                   let uu____5217 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5217, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5235 = resolvex loc env1 x  in
              (match uu____5235 with
               | (loc1,env2,xbv) ->
                   let uu____5267 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5267, []))
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
              let uu____5281 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5281, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5309;_},args)
              ->
              let uu____5315 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5376  ->
                       match uu____5376 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5457 = aux loc1 env2 arg  in
                           (match uu____5457 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5315 with
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
                   let uu____5629 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5629, annots))
          | FStar_Parser_AST.PatApp uu____5645 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5673 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5723  ->
                       match uu____5723 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5784 = aux loc1 env2 pat  in
                           (match uu____5784 with
                            | (loc2,env3,uu____5823,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5673 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5917 =
                       let uu____5920 =
                         let uu____5927 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5927  in
                       let uu____5928 =
                         let uu____5929 =
                           let uu____5943 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5943, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5929  in
                       FStar_All.pipe_left uu____5920 uu____5928  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5977 =
                              let uu____5978 =
                                let uu____5992 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5992, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5978  in
                            FStar_All.pipe_left (pos_r r) uu____5977) pats1
                       uu____5917
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
              let uu____6048 =
                FStar_List.fold_left
                  (fun uu____6107  ->
                     fun p2  ->
                       match uu____6107 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6189 = aux loc1 env2 p2  in
                           (match uu____6189 with
                            | (loc2,env3,uu____6233,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6048 with
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
                     | uu____6396 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6399 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6399, annots))
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
                     (fun uu____6475  ->
                        match uu____6475 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6505  ->
                        match uu____6505 with
                        | (f,uu____6511) ->
                            let uu____6512 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6538  ->
                                      match uu____6538 with
                                      | (g,uu____6545) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6512 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6551,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6558 =
                  let uu____6559 =
                    let uu____6566 =
                      let uu____6567 =
                        let uu____6568 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6568  in
                      FStar_Parser_AST.mk_pattern uu____6567
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6566, args)  in
                  FStar_Parser_AST.PatApp uu____6559  in
                FStar_Parser_AST.mk_pattern uu____6558
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6571 = aux loc env1 app  in
              (match uu____6571 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6648 =
                           let uu____6649 =
                             let uu____6663 =
                               let uu___1110_6664 = fv  in
                               let uu____6665 =
                                 let uu____6668 =
                                   let uu____6669 =
                                     let uu____6676 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6676)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6669
                                    in
                                 FStar_Pervasives_Native.Some uu____6668  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6664.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6664.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6665
                               }  in
                             (uu____6663, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6649  in
                         FStar_All.pipe_left pos uu____6648
                     | uu____6702 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6786 = aux' true loc env1 p2  in
              (match uu____6786 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6839 =
                     FStar_List.fold_left
                       (fun uu____6887  ->
                          fun p4  ->
                            match uu____6887 with
                            | (loc2,env3,ps1) ->
                                let uu____6952 = aux' true loc2 env3 p4  in
                                (match uu____6952 with
                                 | (loc3,env4,uu____6990,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6839 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7151 ->
              let uu____7152 = aux' true loc env1 p1  in
              (match uu____7152 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7243 = aux_maybe_or env p  in
        match uu____7243 with
        | (env1,b,pats) ->
            ((let uu____7298 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7298
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
            let uu____7372 =
              let uu____7373 =
                let uu____7384 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7384, (ty, tacopt))  in
              LetBinder uu____7373  in
            (env, uu____7372, [])  in
          let op_to_ident x =
            let uu____7401 =
              let uu____7407 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7407, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7401  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7420 = op_to_ident x  in
              mklet uu____7420 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7422) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7428;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7444 = op_to_ident x  in
              let uu____7445 = desugar_term env t  in
              mklet uu____7444 uu____7445 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7447);
                 FStar_Parser_AST.prange = uu____7448;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7468 = desugar_term env t  in
              mklet x uu____7468 tacopt1
          | uu____7469 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7482 = desugar_data_pat true env p  in
           match uu____7482 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7512;
                      FStar_Syntax_Syntax.p = uu____7513;_},uu____7514)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7527;
                      FStar_Syntax_Syntax.p = uu____7528;_},uu____7529)::[]
                     -> []
                 | uu____7542 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7550  ->
    fun env  ->
      fun pat  ->
        let uu____7554 = desugar_data_pat false env pat  in
        match uu____7554 with | (env1,uu____7571,pat1) -> (env1, pat1)

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
      let uu____7593 = desugar_term_aq env e  in
      match uu____7593 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7612 = desugar_typ_aq env e  in
      match uu____7612 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7622  ->
        fun range  ->
          match uu____7622 with
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
              ((let uu____7644 =
                  let uu____7646 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7646  in
                if uu____7644
                then
                  let uu____7649 =
                    let uu____7655 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7655)  in
                  FStar_Errors.log_issue range uu____7649
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
                  let uu____7676 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7676 range  in
                let lid1 =
                  let uu____7680 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7680 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7690 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7690 range  in
                           let private_fv =
                             let uu____7692 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7692 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7693 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7693.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7693.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7694 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7698 =
                        let uu____7704 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7704)
                         in
                      FStar_Errors.raise_error uu____7698 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7724 =
                  let uu____7731 =
                    let uu____7732 =
                      let uu____7749 =
                        let uu____7760 =
                          let uu____7769 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7769)  in
                        [uu____7760]  in
                      (lid1, uu____7749)  in
                    FStar_Syntax_Syntax.Tm_app uu____7732  in
                  FStar_Syntax_Syntax.mk uu____7731  in
                uu____7724 FStar_Pervasives_Native.None range))

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
          let uu___1293_7888 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7888.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7888.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7891 =
          let uu____7892 = unparen top  in uu____7892.FStar_Parser_AST.tm  in
        match uu____7891 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7897 ->
            let uu____7906 = desugar_formula env top  in (uu____7906, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7915 = desugar_formula env t  in (uu____7915, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7924 = desugar_formula env t  in (uu____7924, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7951 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7951, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7953 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7953, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7962 =
                let uu____7963 =
                  let uu____7970 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7970, args)  in
                FStar_Parser_AST.Op uu____7963  in
              FStar_Parser_AST.mk_term uu____7962 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7975 =
              let uu____7976 =
                let uu____7977 =
                  let uu____7984 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7984, [e])  in
                FStar_Parser_AST.Op uu____7977  in
              FStar_Parser_AST.mk_term uu____7976 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7975
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7996 = FStar_Ident.text_of_id op_star  in
             uu____7996 = "*") &&
              (let uu____8001 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8001 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8018;_},t1::t2::[])
                  when
                  let uu____8024 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8024 FStar_Option.isNone ->
                  let uu____8031 = flatten1 t1  in
                  FStar_List.append uu____8031 [t2]
              | uu____8034 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1341_8039 = top  in
              let uu____8040 =
                let uu____8041 =
                  let uu____8052 =
                    FStar_List.map
                      (fun uu____8063  -> FStar_Util.Inr uu____8063) terms
                     in
                  (uu____8052, rhs)  in
                FStar_Parser_AST.Sum uu____8041  in
              {
                FStar_Parser_AST.tm = uu____8040;
                FStar_Parser_AST.range =
                  (uu___1341_8039.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1341_8039.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8071 =
              let uu____8072 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8072  in
            (uu____8071, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8078 =
              let uu____8084 =
                let uu____8086 =
                  let uu____8088 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8088 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8086  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8084)  in
            FStar_Errors.raise_error uu____8078 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8103 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8103 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8110 =
                   let uu____8116 =
                     let uu____8118 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8118
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8116)
                    in
                 FStar_Errors.raise_error uu____8110
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8133 =
                     let uu____8158 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8220 = desugar_term_aq env t  in
                               match uu____8220 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8158 FStar_List.unzip  in
                   (match uu____8133 with
                    | (args1,aqs) ->
                        let uu____8353 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8353, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8370)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8387 =
              let uu___1370_8388 = top  in
              let uu____8389 =
                let uu____8390 =
                  let uu____8397 =
                    let uu___1372_8398 = top  in
                    let uu____8399 =
                      let uu____8400 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8400  in
                    {
                      FStar_Parser_AST.tm = uu____8399;
                      FStar_Parser_AST.range =
                        (uu___1372_8398.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1372_8398.FStar_Parser_AST.level)
                    }  in
                  (uu____8397, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8390  in
              {
                FStar_Parser_AST.tm = uu____8389;
                FStar_Parser_AST.range =
                  (uu___1370_8388.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1370_8388.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8387
        | FStar_Parser_AST.Construct (n1,(a,uu____8403)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8423 =
                let uu___1382_8424 = top  in
                let uu____8425 =
                  let uu____8426 =
                    let uu____8433 =
                      let uu___1384_8434 = top  in
                      let uu____8435 =
                        let uu____8436 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8436  in
                      {
                        FStar_Parser_AST.tm = uu____8435;
                        FStar_Parser_AST.range =
                          (uu___1384_8434.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1384_8434.FStar_Parser_AST.level)
                      }  in
                    (uu____8433, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8426  in
                {
                  FStar_Parser_AST.tm = uu____8425;
                  FStar_Parser_AST.range =
                    (uu___1382_8424.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1382_8424.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8423))
        | FStar_Parser_AST.Construct (n1,(a,uu____8439)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8456 =
              let uu___1393_8457 = top  in
              let uu____8458 =
                let uu____8459 =
                  let uu____8466 =
                    let uu___1395_8467 = top  in
                    let uu____8468 =
                      let uu____8469 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8469  in
                    {
                      FStar_Parser_AST.tm = uu____8468;
                      FStar_Parser_AST.range =
                        (uu___1395_8467.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1395_8467.FStar_Parser_AST.level)
                    }  in
                  (uu____8466, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8459  in
              {
                FStar_Parser_AST.tm = uu____8458;
                FStar_Parser_AST.range =
                  (uu___1393_8457.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1393_8457.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8456
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8470; FStar_Ident.ident = uu____8471;
              FStar_Ident.nsstr = uu____8472; FStar_Ident.str = "Type0";_}
            ->
            let uu____8477 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8477, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8478; FStar_Ident.ident = uu____8479;
              FStar_Ident.nsstr = uu____8480; FStar_Ident.str = "Type";_}
            ->
            let uu____8485 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8485, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8486; FStar_Ident.ident = uu____8487;
               FStar_Ident.nsstr = uu____8488; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8508 =
              let uu____8509 =
                let uu____8510 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8510  in
              mk1 uu____8509  in
            (uu____8508, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8511; FStar_Ident.ident = uu____8512;
              FStar_Ident.nsstr = uu____8513; FStar_Ident.str = "Effect";_}
            ->
            let uu____8518 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8518, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8519; FStar_Ident.ident = uu____8520;
              FStar_Ident.nsstr = uu____8521; FStar_Ident.str = "True";_}
            ->
            let uu____8526 =
              let uu____8527 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8527
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8526, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8528; FStar_Ident.ident = uu____8529;
              FStar_Ident.nsstr = uu____8530; FStar_Ident.str = "False";_}
            ->
            let uu____8535 =
              let uu____8536 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8536
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8535, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8539;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let uu____8541 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8541 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8550 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8550, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8552 =
                   let uu____8554 = FStar_Ident.text_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8554 txt
                    in
                 failwith uu____8552)
        | FStar_Parser_AST.Var l ->
            let uu____8562 = desugar_name mk1 setpos env true l  in
            (uu____8562, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8570 = desugar_name mk1 setpos env true l  in
            (uu____8570, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8587 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8587 with
              | FStar_Pervasives_Native.Some uu____8597 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8605 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8605 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8623 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8644 =
                   let uu____8645 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk1 setpos env resolve uu____8645  in
                 (uu____8644, noaqs)
             | uu____8651 ->
                 let uu____8659 =
                   let uu____8665 =
                     FStar_Util.format1
                       "Data constructor or effect %s not found"
                       l.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8665)  in
                 FStar_Errors.raise_error uu____8659
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8674 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8674 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8681 =
                   let uu____8687 =
                     FStar_Util.format1 "Data constructor %s not found"
                       lid.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8687)
                    in
                 FStar_Errors.raise_error uu____8681
                   top.FStar_Parser_AST.range
             | uu____8695 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8699 = desugar_name mk1 setpos env true lid'  in
                 (uu____8699, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8720 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8720 with
             | FStar_Pervasives_Native.Some head1 ->
                 let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                 (match args with
                  | [] -> (head2, noaqs)
                  | uu____8739 ->
                      let uu____8746 =
                        FStar_Util.take
                          (fun uu____8770  ->
                             match uu____8770 with
                             | (uu____8776,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8746 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8821 =
                             let uu____8846 =
                               FStar_List.map
                                 (fun uu____8889  ->
                                    match uu____8889 with
                                    | (t,imp) ->
                                        let uu____8906 =
                                          desugar_term_aq env t  in
                                        (match uu____8906 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8846 FStar_List.unzip
                              in
                           (match uu____8821 with
                            | (args2,aqs) ->
                                let head3 =
                                  if universes1 = []
                                  then head2
                                  else
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head2, universes1))
                                   in
                                let uu____9049 =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head3, args2))
                                   in
                                (uu____9049, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9068 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9068 with
                   | FStar_Pervasives_Native.None  ->
                       (FStar_Errors.Fatal_ConstructorNotFound,
                         (Prims.op_Hat "Constructor "
                            (Prims.op_Hat l.FStar_Ident.str " not found")))
                   | FStar_Pervasives_Native.Some uu____9079 ->
                       (FStar_Errors.Fatal_UnexpectedEffect,
                         (Prims.op_Hat "Effect "
                            (Prims.op_Hat l.FStar_Ident.str
                               " used at an unexpected position")))
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9107  ->
                 match uu___8_9107 with
                 | FStar_Util.Inr uu____9113 -> true
                 | uu____9115 -> false) binders
            ->
            let terms =
              let uu____9124 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9141  ->
                        match uu___9_9141 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9147 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9124 [t]  in
            let uu____9149 =
              let uu____9174 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9231 = desugar_typ_aq env t1  in
                        match uu____9231 with
                        | (t',aq) ->
                            let uu____9242 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9242, aq)))
                 in
              FStar_All.pipe_right uu____9174 FStar_List.unzip  in
            (match uu____9149 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9352 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9352
                    in
                 let uu____9361 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9361, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9388 =
              let uu____9405 =
                let uu____9412 =
                  let uu____9419 =
                    FStar_All.pipe_left
                      (fun uu____9428  -> FStar_Util.Inl uu____9428)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9419]  in
                FStar_List.append binders uu____9412  in
              FStar_List.fold_left
                (fun uu____9473  ->
                   fun b  ->
                     match uu____9473 with
                     | (env1,tparams,typs) ->
                         let uu____9534 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9549 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9549)
                            in
                         (match uu____9534 with
                          | (xopt,t1) ->
                              let uu____9574 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9583 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9583)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9574 with
                               | (env2,x) ->
                                   let uu____9603 =
                                     let uu____9606 =
                                       let uu____9609 =
                                         let uu____9610 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9610
                                          in
                                       [uu____9609]  in
                                     FStar_List.append typs uu____9606  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1549_9636 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1549_9636.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1549_9636.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9603)))) (env, [], []) uu____9405
               in
            (match uu____9388 with
             | (env1,uu____9664,targs) ->
                 let tup =
                   let uu____9687 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9687
                    in
                 let uu____9688 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9688, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9707 = uncurry binders t  in
            (match uu____9707 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9751 =
                   match uu___10_9751 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9768 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9768
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9792 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9792 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9825 = aux env [] bs  in (uu____9825, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9834 = desugar_binder env b  in
            (match uu____9834 with
             | (FStar_Pervasives_Native.None ,uu____9845) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9860 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9860 with
                  | ((x,uu____9876),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9889 =
                        let uu____9890 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9890  in
                      (uu____9889, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9968 = FStar_Util.set_is_empty i  in
                    if uu____9968
                    then
                      let uu____9973 = FStar_Util.set_union acc set1  in
                      aux uu____9973 sets2
                    else
                      (let uu____9978 =
                         let uu____9979 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9979  in
                       FStar_Pervasives_Native.Some uu____9978)
                 in
              let uu____9982 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9982 sets  in
            ((let uu____9986 = check_disjoint bvss  in
              match uu____9986 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9990 =
                    let uu____9996 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9996)
                     in
                  let uu____10000 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9990 uu____10000);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10008 =
                FStar_List.fold_left
                  (fun uu____10028  ->
                     fun pat  ->
                       match uu____10028 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10054,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10064 =
                                  let uu____10067 = free_type_vars env1 t  in
                                  FStar_List.append uu____10067 ftvs  in
                                (env1, uu____10064)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10072,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10083 =
                                  let uu____10086 = free_type_vars env1 t  in
                                  let uu____10089 =
                                    let uu____10092 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10092 ftvs  in
                                  FStar_List.append uu____10086 uu____10089
                                   in
                                (env1, uu____10083)
                            | uu____10097 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10008 with
              | (uu____10106,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10118 =
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
                    FStar_List.append uu____10118 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10198 = desugar_term_aq env1 body  in
                        (match uu____10198 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10233 =
                                       let uu____10234 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10234
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10233
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
                             let uu____10303 =
                               let uu____10304 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10304  in
                             (uu____10303, aq))
                    | p::rest ->
                        let uu____10317 = desugar_binding_pat env1 p  in
                        (match uu____10317 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10349)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10364 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10373 =
                               match b with
                               | LetBinder uu____10414 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10483) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10537 =
                                           let uu____10546 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10546, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10537
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10608,uu____10609) ->
                                              let tup2 =
                                                let uu____10611 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10611
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10616 =
                                                  let uu____10623 =
                                                    let uu____10624 =
                                                      let uu____10641 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10644 =
                                                        let uu____10655 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10664 =
                                                          let uu____10675 =
                                                            let uu____10684 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10684
                                                             in
                                                          [uu____10675]  in
                                                        uu____10655 ::
                                                          uu____10664
                                                         in
                                                      (uu____10641,
                                                        uu____10644)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10624
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10623
                                                   in
                                                uu____10616
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10732 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10732
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10783,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10785,pats1)) ->
                                              let tupn =
                                                let uu____10830 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10830
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10843 =
                                                  let uu____10844 =
                                                    let uu____10861 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10864 =
                                                      let uu____10875 =
                                                        let uu____10886 =
                                                          let uu____10895 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10895
                                                           in
                                                        [uu____10886]  in
                                                      FStar_List.append args
                                                        uu____10875
                                                       in
                                                    (uu____10861,
                                                      uu____10864)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10844
                                                   in
                                                mk1 uu____10843  in
                                              let p2 =
                                                let uu____10943 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10943
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10990 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10373 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11082,uu____11083,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11105 =
                let uu____11106 = unparen e  in
                uu____11106.FStar_Parser_AST.tm  in
              match uu____11105 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11116 ->
                  let uu____11117 = desugar_term_aq env e  in
                  (match uu____11117 with
                   | (head1,aq) ->
                       let uu____11130 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11130, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11137 ->
            let rec aux args aqs e =
              let uu____11214 =
                let uu____11215 = unparen e  in
                uu____11215.FStar_Parser_AST.tm  in
              match uu____11214 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11233 = desugar_term_aq env t  in
                  (match uu____11233 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11281 ->
                  let uu____11282 = desugar_term_aq env e  in
                  (match uu____11282 with
                   | (head1,aq) ->
                       let uu____11303 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11303, (join_aqs (aq :: aqs))))
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
            let uu____11366 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11366
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
            let uu____11418 = desugar_term_aq env t  in
            (match uu____11418 with
             | (tm,s) ->
                 let uu____11429 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11429, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11435 =
              let uu____11448 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11448 then desugar_typ_aq else desugar_term_aq  in
            uu____11435 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11515 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11658  ->
                        match uu____11658 with
                        | (attr_opt,(p,def)) ->
                            let uu____11716 = is_app_pattern p  in
                            if uu____11716
                            then
                              let uu____11749 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11749, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11832 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11832, def1)
                               | uu____11877 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11915);
                                           FStar_Parser_AST.prange =
                                             uu____11916;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11965 =
                                            let uu____11986 =
                                              let uu____11991 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11991  in
                                            (uu____11986, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11965, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12083) ->
                                        if top_level
                                        then
                                          let uu____12119 =
                                            let uu____12140 =
                                              let uu____12145 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12145  in
                                            (uu____12140, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12119, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12236 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12269 =
                FStar_List.fold_left
                  (fun uu____12358  ->
                     fun uu____12359  ->
                       match (uu____12358, uu____12359) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12489,uu____12490),uu____12491))
                           ->
                           let uu____12625 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12665 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12665 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12700 =
                                        let uu____12703 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12703 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12700, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12719 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12719 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12625 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12269 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12972 =
                    match uu____12972 with
                    | (attrs_opt,(uu____13012,args,result_t),def) ->
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
                                let uu____13104 = is_comp_type env1 t  in
                                if uu____13104
                                then
                                  ((let uu____13108 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13118 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13118))
                                       in
                                    match uu____13108 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13125 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13128 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13128))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13125
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
                          | uu____13139 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13142 = desugar_term_aq env1 def2  in
                        (match uu____13142 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13164 =
                                     let uu____13165 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13165
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13164
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
                  let uu____13206 =
                    let uu____13223 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13223 FStar_List.unzip  in
                  (match uu____13206 with
                   | (lbs1,aqss) ->
                       let uu____13365 = desugar_term_aq env' body  in
                       (match uu____13365 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13471  ->
                                    fun used_marker  ->
                                      match uu____13471 with
                                      | (_attr_opt,(f,uu____13545,uu____13546),uu____13547)
                                          ->
                                          let uu____13604 =
                                            let uu____13606 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13606  in
                                          if uu____13604
                                          then
                                            let uu____13630 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13648 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13650 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13648, "Local",
                                                    uu____13650)
                                              | FStar_Util.Inr l ->
                                                  let uu____13655 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13657 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13655, "Global",
                                                    uu____13657)
                                               in
                                            (match uu____13630 with
                                             | (nm,gl,rng) ->
                                                 let uu____13668 =
                                                   let uu____13674 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13674)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13668)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13682 =
                                let uu____13685 =
                                  let uu____13686 =
                                    let uu____13700 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13700)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13686  in
                                FStar_All.pipe_left mk1 uu____13685  in
                              (uu____13682,
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
              let uu____13802 = desugar_term_aq env t1  in
              match uu____13802 with
              | (t11,aq0) ->
                  let uu____13823 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13823 with
                   | (env1,binder,pat1) ->
                       let uu____13853 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13895 = desugar_term_aq env1 t2  in
                             (match uu____13895 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13917 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13917
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13918 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13918, aq))
                         | LocalBinder (x,uu____13959) ->
                             let uu____13960 = desugar_term_aq env1 t2  in
                             (match uu____13960 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13982;
                                         FStar_Syntax_Syntax.p = uu____13983;_},uu____13984)::[]
                                        -> body1
                                    | uu____13997 ->
                                        let uu____14000 =
                                          let uu____14007 =
                                            let uu____14008 =
                                              let uu____14031 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14034 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14031, uu____14034)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14008
                                             in
                                          FStar_Syntax_Syntax.mk uu____14007
                                           in
                                        uu____14000
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14071 =
                                    let uu____14074 =
                                      let uu____14075 =
                                        let uu____14089 =
                                          let uu____14092 =
                                            let uu____14093 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14093]  in
                                          FStar_Syntax_Subst.close
                                            uu____14092 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14089)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14075
                                       in
                                    FStar_All.pipe_left mk1 uu____14074  in
                                  (uu____14071, aq))
                          in
                       (match uu____13853 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14201 = FStar_List.hd lbs  in
            (match uu____14201 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14245 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14245
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14261 =
                let uu____14262 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14262  in
              mk1 uu____14261  in
            let uu____14263 = desugar_term_aq env t1  in
            (match uu____14263 with
             | (t1',aq1) ->
                 let uu____14274 = desugar_term_aq env t2  in
                 (match uu____14274 with
                  | (t2',aq2) ->
                      let uu____14285 = desugar_term_aq env t3  in
                      (match uu____14285 with
                       | (t3',aq3) ->
                           let uu____14296 =
                             let uu____14297 =
                               let uu____14298 =
                                 let uu____14321 =
                                   let uu____14338 =
                                     let uu____14353 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14353,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14367 =
                                     let uu____14384 =
                                       let uu____14399 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14399,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14384]  in
                                   uu____14338 :: uu____14367  in
                                 (t1', uu____14321)  in
                               FStar_Syntax_Syntax.Tm_match uu____14298  in
                             mk1 uu____14297  in
                           (uu____14296, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14595 =
              match uu____14595 with
              | (pat,wopt,b) ->
                  let uu____14617 = desugar_match_pat env pat  in
                  (match uu____14617 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14648 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14648
                          in
                       let uu____14653 = desugar_term_aq env1 b  in
                       (match uu____14653 with
                        | (b1,aq) ->
                            let uu____14666 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14666, aq)))
               in
            let uu____14671 = desugar_term_aq env e  in
            (match uu____14671 with
             | (e1,aq) ->
                 let uu____14682 =
                   let uu____14713 =
                     let uu____14746 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14746 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14713
                     (fun uu____14964  ->
                        match uu____14964 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14682 with
                  | (brs,aqs) ->
                      let uu____15183 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15183, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15217 =
              let uu____15238 = is_comp_type env t  in
              if uu____15238
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15293 = desugar_term_aq env t  in
                 match uu____15293 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15217 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15385 = desugar_term_aq env e  in
                 (match uu____15385 with
                  | (e1,aq) ->
                      let uu____15396 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15396, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15435,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15478 = FStar_List.hd fields  in
              match uu____15478 with | (f,uu____15490) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15536  ->
                        match uu____15536 with
                        | (g,uu____15543) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15550,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15564 =
                         let uu____15570 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15570)
                          in
                       FStar_Errors.raise_error uu____15564
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
                  let uu____15581 =
                    let uu____15592 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15623  ->
                              match uu____15623 with
                              | (f,uu____15633) ->
                                  let uu____15634 =
                                    let uu____15635 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15635
                                     in
                                  (uu____15634, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15592)  in
                  FStar_Parser_AST.Construct uu____15581
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15653 =
                      let uu____15654 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15654  in
                    FStar_Parser_AST.mk_term uu____15653
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15656 =
                      let uu____15669 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15699  ->
                                match uu____15699 with
                                | (f,uu____15709) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15669)  in
                    FStar_Parser_AST.Record uu____15656  in
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
            let uu____15769 = desugar_term_aq env recterm1  in
            (match uu____15769 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15785;
                         FStar_Syntax_Syntax.vars = uu____15786;_},args)
                      ->
                      let uu____15812 =
                        let uu____15813 =
                          let uu____15814 =
                            let uu____15831 =
                              let uu____15834 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15835 =
                                let uu____15838 =
                                  let uu____15839 =
                                    let uu____15846 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15846)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15839
                                   in
                                FStar_Pervasives_Native.Some uu____15838  in
                              FStar_Syntax_Syntax.fvar uu____15834
                                FStar_Syntax_Syntax.delta_constant
                                uu____15835
                               in
                            (uu____15831, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15814  in
                        FStar_All.pipe_left mk1 uu____15813  in
                      (uu____15812, s)
                  | uu____15875 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15878 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15878 with
             | (constrname,is_rec) ->
                 let uu____15897 = desugar_term_aq env e  in
                 (match uu____15897 with
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
                      let uu____15917 =
                        let uu____15918 =
                          let uu____15919 =
                            let uu____15936 =
                              let uu____15939 =
                                let uu____15940 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15940
                                 in
                              FStar_Syntax_Syntax.fvar uu____15939
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15942 =
                              let uu____15953 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____15953]  in
                            (uu____15936, uu____15942)  in
                          FStar_Syntax_Syntax.Tm_app uu____15919  in
                        FStar_All.pipe_left mk1 uu____15918  in
                      (uu____15917, s)))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____15993 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____15993
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16004 =
              let uu____16005 = FStar_Syntax_Subst.compress tm  in
              uu____16005.FStar_Syntax_Syntax.n  in
            (match uu____16004 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16013 =
                   let uu___2117_16014 =
                     let uu____16015 =
                       let uu____16017 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16017  in
                     FStar_Syntax_Util.exp_string uu____16015  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2117_16014.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2117_16014.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16013, noaqs)
             | uu____16018 ->
                 let uu____16019 =
                   let uu____16025 =
                     let uu____16027 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16027
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16025)  in
                 FStar_Errors.raise_error uu____16019
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16036 = desugar_term_aq env e  in
            (match uu____16036 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16048 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16048, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16053 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16054 =
              let uu____16055 =
                let uu____16062 = desugar_term env e  in (bv, uu____16062)
                 in
              [uu____16055]  in
            (uu____16053, uu____16054)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16087 =
              let uu____16088 =
                let uu____16089 =
                  let uu____16096 = desugar_term env e  in (uu____16096, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16089  in
              FStar_All.pipe_left mk1 uu____16088  in
            (uu____16087, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16125 -> false  in
              let uu____16127 =
                let uu____16128 = unparen rel1  in
                uu____16128.FStar_Parser_AST.tm  in
              match uu____16127 with
              | FStar_Parser_AST.Op (id1,uu____16131) ->
                  let uu____16136 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16136 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16144 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16144 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16155 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16155 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16161 -> false  in
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
              let uu____16182 =
                let uu____16183 =
                  let uu____16190 =
                    let uu____16191 =
                      let uu____16192 =
                        let uu____16201 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16214 =
                          let uu____16215 =
                            let uu____16216 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16216  in
                          FStar_Parser_AST.mk_term uu____16215
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16201, uu____16214,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16192  in
                    FStar_Parser_AST.mk_term uu____16191
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16190)  in
                FStar_Parser_AST.Abs uu____16183  in
              FStar_Parser_AST.mk_term uu____16182
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
              let uu____16237 = FStar_List.last steps  in
              match uu____16237 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16240,uu____16241,last_expr)) -> last_expr
              | uu____16243 -> failwith "impossible: no last_expr on calc"
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
            let uu____16271 =
              FStar_List.fold_left
                (fun uu____16289  ->
                   fun uu____16290  ->
                     match (uu____16289, uu____16290) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16313 = is_impl rel2  in
                           if uu____16313
                           then
                             let uu____16316 =
                               let uu____16323 =
                                 let uu____16328 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16328, FStar_Parser_AST.Nothing)  in
                               [uu____16323]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16316 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16340 =
                             let uu____16347 =
                               let uu____16354 =
                                 let uu____16361 =
                                   let uu____16368 =
                                     let uu____16373 = eta_and_annot rel2  in
                                     (uu____16373, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16374 =
                                     let uu____16381 =
                                       let uu____16388 =
                                         let uu____16393 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16393,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16394 =
                                         let uu____16401 =
                                           let uu____16406 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16406,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16401]  in
                                       uu____16388 :: uu____16394  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16381
                                      in
                                   uu____16368 :: uu____16374  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16361
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16354
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16347
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16340
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16271 with
             | (e1,uu____16444) ->
                 let e2 =
                   let uu____16446 =
                     let uu____16453 =
                       let uu____16460 =
                         let uu____16467 =
                           let uu____16472 = FStar_Parser_AST.thunk e1  in
                           (uu____16472, FStar_Parser_AST.Nothing)  in
                         [uu____16467]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16460  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16453  in
                   FStar_Parser_AST.mkApp finish1 uu____16446
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16489 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16490 = desugar_formula env top  in
            (uu____16490, noaqs)
        | uu____16491 ->
            let uu____16492 =
              let uu____16498 =
                let uu____16500 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16500  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16498)  in
            FStar_Errors.raise_error uu____16492 top.FStar_Parser_AST.range

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
           (fun uu____16544  ->
              match uu____16544 with
              | (a,imp) ->
                  let uu____16557 = desugar_term env a  in
                  arg_withimp_e imp uu____16557))

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
          let is_requires uu____16594 =
            match uu____16594 with
            | (t1,uu____16601) ->
                let uu____16602 =
                  let uu____16603 = unparen t1  in
                  uu____16603.FStar_Parser_AST.tm  in
                (match uu____16602 with
                 | FStar_Parser_AST.Requires uu____16605 -> true
                 | uu____16614 -> false)
             in
          let is_ensures uu____16626 =
            match uu____16626 with
            | (t1,uu____16633) ->
                let uu____16634 =
                  let uu____16635 = unparen t1  in
                  uu____16635.FStar_Parser_AST.tm  in
                (match uu____16634 with
                 | FStar_Parser_AST.Ensures uu____16637 -> true
                 | uu____16646 -> false)
             in
          let is_app head1 uu____16664 =
            match uu____16664 with
            | (t1,uu____16672) ->
                let uu____16673 =
                  let uu____16674 = unparen t1  in
                  uu____16674.FStar_Parser_AST.tm  in
                (match uu____16673 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16677;
                        FStar_Parser_AST.level = uu____16678;_},uu____16679,uu____16680)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16682 -> false)
             in
          let is_smt_pat uu____16694 =
            match uu____16694 with
            | (t1,uu____16701) ->
                let uu____16702 =
                  let uu____16703 = unparen t1  in
                  uu____16703.FStar_Parser_AST.tm  in
                (match uu____16702 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16707);
                               FStar_Parser_AST.range = uu____16708;
                               FStar_Parser_AST.level = uu____16709;_},uu____16710)::uu____16711::[])
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
                               FStar_Parser_AST.range = uu____16760;
                               FStar_Parser_AST.level = uu____16761;_},uu____16762)::uu____16763::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16796 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16831 = head_and_args t1  in
            match uu____16831 with
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
                     let thunk_ens uu____16924 =
                       match uu____16924 with
                       | (e,i) ->
                           let uu____16935 = FStar_Parser_AST.thunk e  in
                           (uu____16935, i)
                        in
                     let fail_lemma uu____16947 =
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
                           let uu____17053 =
                             let uu____17060 =
                               let uu____17067 = thunk_ens ens  in
                               [uu____17067; nil_pat]  in
                             req_true :: uu____17060  in
                           unit_tm :: uu____17053
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17114 =
                             let uu____17121 =
                               let uu____17128 = thunk_ens ens  in
                               [uu____17128; nil_pat]  in
                             req :: uu____17121  in
                           unit_tm :: uu____17114
                       | ens::smtpat::[] when
                           (((let uu____17177 = is_requires ens  in
                              Prims.op_Negation uu____17177) &&
                               (let uu____17180 = is_smt_pat ens  in
                                Prims.op_Negation uu____17180))
                              &&
                              (let uu____17183 = is_decreases ens  in
                               Prims.op_Negation uu____17183))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17185 =
                             let uu____17192 =
                               let uu____17199 = thunk_ens ens  in
                               [uu____17199; smtpat]  in
                             req_true :: uu____17192  in
                           unit_tm :: uu____17185
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17246 =
                             let uu____17253 =
                               let uu____17260 = thunk_ens ens  in
                               [uu____17260; nil_pat; dec]  in
                             req_true :: uu____17253  in
                           unit_tm :: uu____17246
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17320 =
                             let uu____17327 =
                               let uu____17334 = thunk_ens ens  in
                               [uu____17334; smtpat; dec]  in
                             req_true :: uu____17327  in
                           unit_tm :: uu____17320
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17394 =
                             let uu____17401 =
                               let uu____17408 = thunk_ens ens  in
                               [uu____17408; nil_pat; dec]  in
                             req :: uu____17401  in
                           unit_tm :: uu____17394
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17468 =
                             let uu____17475 =
                               let uu____17482 = thunk_ens ens  in
                               [uu____17482; smtpat]  in
                             req :: uu____17475  in
                           unit_tm :: uu____17468
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17547 =
                             let uu____17554 =
                               let uu____17561 = thunk_ens ens  in
                               [uu____17561; dec; smtpat]  in
                             req :: uu____17554  in
                           unit_tm :: uu____17547
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17623 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17623, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17651 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17651
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17654 =
                       let uu____17661 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17661, [])  in
                     (uu____17654, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17679 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17679
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17682 =
                       let uu____17689 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17689, [])  in
                     (uu____17682, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17711 =
                       let uu____17718 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17718, [])  in
                     (uu____17711, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17741 when allow_type_promotion ->
                     let default_effect =
                       let uu____17743 = FStar_Options.ml_ish ()  in
                       if uu____17743
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17749 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17749
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17756 =
                       let uu____17763 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17763, [])  in
                     (uu____17756, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17786 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17805 = pre_process_comp_typ t  in
          match uu____17805 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17857 =
                    let uu____17863 =
                      let uu____17865 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17865
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17863)
                     in
                  fail1 uu____17857)
               else ();
               (let is_universe uu____17881 =
                  match uu____17881 with
                  | (uu____17887,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17889 = FStar_Util.take is_universe args  in
                match uu____17889 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17948  ->
                           match uu____17948 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17955 =
                      let uu____17970 = FStar_List.hd args1  in
                      let uu____17979 = FStar_List.tl args1  in
                      (uu____17970, uu____17979)  in
                    (match uu____17955 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18034 =
                           let is_decrease uu____18073 =
                             match uu____18073 with
                             | (t1,uu____18084) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18095;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18096;_},uu____18097::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18136 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18034 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18253  ->
                                        match uu____18253 with
                                        | (t1,uu____18263) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18272,(arg,uu____18274)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18313 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18334 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18346 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18346
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18353 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18353
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18363 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18363
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18370 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18370
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18377 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18377
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18384 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18384
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18405 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18405
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
                                                    let uu____18496 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18496
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
                                              | uu____18517 -> pat  in
                                            let uu____18518 =
                                              let uu____18529 =
                                                let uu____18540 =
                                                  let uu____18549 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18549, aq)  in
                                                [uu____18540]  in
                                              ens :: uu____18529  in
                                            req :: uu____18518
                                        | uu____18590 -> rest2
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
        let uu___2442_18625 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2442_18625.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2442_18625.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2449_18679 = b  in
             {
               FStar_Parser_AST.b = (uu___2449_18679.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2449_18679.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2449_18679.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18708 body1 =
          match uu____18708 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18754::uu____18755) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18773 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2468_18800 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2468_18800.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2468_18800.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18863 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18863))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18894 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18894 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2481_18904 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2481_18904.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2481_18904.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18910 =
                     let uu____18913 =
                       let uu____18914 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18914]  in
                     no_annot_abs uu____18913 body2  in
                   FStar_All.pipe_left setpos uu____18910  in
                 let uu____18935 =
                   let uu____18936 =
                     let uu____18953 =
                       let uu____18956 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18956
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18958 =
                       let uu____18969 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18969]  in
                     (uu____18953, uu____18958)  in
                   FStar_Syntax_Syntax.Tm_app uu____18936  in
                 FStar_All.pipe_left mk1 uu____18935)
        | uu____19008 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19073 = q (rest, pats, body)  in
              let uu____19076 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19073 uu____19076
                FStar_Parser_AST.Formula
               in
            let uu____19077 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19077 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19088 -> failwith "impossible"  in
      let uu____19092 =
        let uu____19093 = unparen f  in uu____19093.FStar_Parser_AST.tm  in
      match uu____19092 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19106,uu____19107) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19131,uu____19132) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19188 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19188
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19232 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19232
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19296 -> desugar_term env f

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
          let uu____19307 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19307)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19312 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19312)
      | FStar_Parser_AST.TVariable x ->
          let uu____19316 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19316)
      | FStar_Parser_AST.NoName t ->
          let uu____19320 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19320)
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
      fun uu___11_19328  ->
        match uu___11_19328 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19350 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19350, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19367 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19367 with
             | (env1,a1) ->
                 let uu____19384 =
                   let uu____19391 = trans_aqual env1 imp  in
                   ((let uu___2581_19397 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2581_19397.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2581_19397.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19391)
                    in
                 (uu____19384, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19405  ->
      match uu___12_19405 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19409 =
            let uu____19410 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19410  in
          FStar_Pervasives_Native.Some uu____19409
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19438 =
        FStar_List.fold_left
          (fun uu____19471  ->
             fun b  ->
               match uu____19471 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2599_19515 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2599_19515.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2599_19515.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2599_19515.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19530 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19530 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2609_19548 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2609_19548.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2609_19548.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19549 =
                               let uu____19556 =
                                 let uu____19561 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19561)  in
                               uu____19556 :: out  in
                             (env2, uu____19549))
                    | uu____19572 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19438 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19660 =
          let uu____19661 = unparen t  in uu____19661.FStar_Parser_AST.tm  in
        match uu____19660 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19662; FStar_Ident.ident = uu____19663;
              FStar_Ident.nsstr = uu____19664; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19669 ->
            let uu____19670 =
              let uu____19676 =
                let uu____19678 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19678  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19676)  in
            FStar_Errors.raise_error uu____19670 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19695) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19697) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19700 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19718 = binder_ident b  in
         FStar_Common.list_of_option uu____19718) bs
  
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
               (fun uu___13_19755  ->
                  match uu___13_19755 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19760 -> false))
           in
        let quals2 q =
          let uu____19774 =
            (let uu____19778 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19778) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19774
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19795 = FStar_Ident.range_of_lid disc_name  in
                let uu____19796 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19795;
                  FStar_Syntax_Syntax.sigquals = uu____19796;
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
            let uu____19836 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19874  ->
                        match uu____19874 with
                        | (x,uu____19885) ->
                            let uu____19890 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19890 with
                             | (field_name,uu____19898) ->
                                 let only_decl =
                                   ((let uu____19903 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19903)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19905 =
                                        let uu____19907 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19907.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19905)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19925 =
                                       FStar_List.filter
                                         (fun uu___14_19929  ->
                                            match uu___14_19929 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19932 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19925
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19947  ->
                                             match uu___15_19947 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19952 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19955 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19955;
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
                                      let uu____19962 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19962
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19973 =
                                        let uu____19978 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19978  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19973;
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
                                      let uu____19982 =
                                        let uu____19983 =
                                          let uu____19990 =
                                            let uu____19993 =
                                              let uu____19994 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19994
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19993]  in
                                          ((false, [lb]), uu____19990)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19983
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19982;
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
            FStar_All.pipe_right uu____19836 FStar_List.flatten
  
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
            (lid,uu____20043,t,uu____20045,n1,uu____20047) when
            let uu____20054 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20054 ->
            let uu____20056 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20056 with
             | (formals,uu____20066) ->
                 (match formals with
                  | [] -> []
                  | uu____20079 ->
                      let filter_records uu___16_20087 =
                        match uu___16_20087 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20090,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20102 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20104 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20104 with
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
                      let uu____20116 = FStar_Util.first_N n1 formals  in
                      (match uu____20116 with
                       | (uu____20145,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20179 -> []
  
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
                        let uu____20273 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20273
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20297 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20297
                        then
                          let uu____20303 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20303
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20307 =
                          let uu____20312 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20312  in
                        let uu____20313 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20319 =
                              let uu____20322 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20322  in
                            FStar_Syntax_Util.arrow typars uu____20319
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20327 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20307;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20313;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20327;
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
          let tycon_id uu___17_20381 =
            match uu___17_20381 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20383,uu____20384) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20394,uu____20395,uu____20396) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20406,uu____20407,uu____20408) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20430,uu____20431,uu____20432) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20470) ->
                let uu____20471 =
                  let uu____20472 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20472  in
                FStar_Parser_AST.mk_term uu____20471 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20474 =
                  let uu____20475 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20475  in
                FStar_Parser_AST.mk_term uu____20474 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20477) ->
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
              | uu____20508 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20516 =
                     let uu____20517 =
                       let uu____20524 = binder_to_term1 b  in
                       (out, uu____20524, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20517  in
                   FStar_Parser_AST.mk_term uu____20516
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20536 =
            match uu___18_20536 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20580  ->
                       match uu____20580 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20588 =
                    let uu____20589 =
                      let uu____20590 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20590  in
                    FStar_Parser_AST.mk_term uu____20589
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20588 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20597 = binder_idents parms  in id1 ::
                    uu____20597
                   in
                (FStar_List.iter
                   (fun uu____20610  ->
                      match uu____20610 with
                      | (f,uu____20616) ->
                          let uu____20617 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20617
                          then
                            let uu____20622 =
                              let uu____20628 =
                                let uu____20630 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20630
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20628)
                               in
                            FStar_Errors.raise_error uu____20622
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20636 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20636)))
            | uu____20690 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20730 =
            match uu___19_20730 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20754 = typars_of_binders _env binders  in
                (match uu____20754 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20790 =
                         let uu____20791 =
                           let uu____20792 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20792  in
                         FStar_Parser_AST.mk_term uu____20791
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20790 binders  in
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
                     let uu____20801 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20801 with
                      | (_env1,uu____20818) ->
                          let uu____20825 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20825 with
                           | (_env2,uu____20842) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20849 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20892 =
              FStar_List.fold_left
                (fun uu____20926  ->
                   fun uu____20927  ->
                     match (uu____20926, uu____20927) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20996 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20996 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20892 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21087 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21087
                | uu____21088 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21096 = desugar_abstract_tc quals env [] tc  in
              (match uu____21096 with
               | (uu____21109,uu____21110,se,uu____21112) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21115,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21134 =
                                 let uu____21136 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21136  in
                               if uu____21134
                               then
                                 let uu____21139 =
                                   let uu____21145 =
                                     let uu____21147 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21147
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21145)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21139
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
                           | uu____21160 ->
                               let uu____21161 =
                                 let uu____21168 =
                                   let uu____21169 =
                                     let uu____21184 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21184)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21169
                                    in
                                 FStar_Syntax_Syntax.mk uu____21168  in
                               uu____21161 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2892_21197 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2892_21197.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2892_21197.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2892_21197.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2892_21197.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21198 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21213 = typars_of_binders env binders  in
              (match uu____21213 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21247 =
                           FStar_Util.for_some
                             (fun uu___20_21250  ->
                                match uu___20_21250 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21253 -> false) quals
                            in
                         if uu____21247
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21261 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21261
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21266 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21272  ->
                               match uu___21_21272 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21275 -> false))
                        in
                     if uu____21266
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21289 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21289
                     then
                       let uu____21295 =
                         let uu____21302 =
                           let uu____21303 = unparen t  in
                           uu____21303.FStar_Parser_AST.tm  in
                         match uu____21302 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21324 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21354)::args_rev ->
                                   let uu____21366 =
                                     let uu____21367 = unparen last_arg  in
                                     uu____21367.FStar_Parser_AST.tm  in
                                   (match uu____21366 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21395 -> ([], args))
                               | uu____21404 -> ([], args)  in
                             (match uu____21324 with
                              | (cattributes,args1) ->
                                  let uu____21443 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21443))
                         | uu____21454 -> (t, [])  in
                       match uu____21295 with
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
                                  (fun uu___22_21477  ->
                                     match uu___22_21477 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21480 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21488)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21508 = tycon_record_as_variant trec  in
              (match uu____21508 with
               | (t,fs) ->
                   let uu____21525 =
                     let uu____21528 =
                       let uu____21529 =
                         let uu____21538 =
                           let uu____21541 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21541  in
                         (uu____21538, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21529  in
                     uu____21528 :: quals  in
                   desugar_tycon env d uu____21525 [t])
          | uu____21546::uu____21547 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21705 = et  in
                match uu____21705 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21915 ->
                         let trec = tc  in
                         let uu____21935 = tycon_record_as_variant trec  in
                         (match uu____21935 with
                          | (t,fs) ->
                              let uu____21991 =
                                let uu____21994 =
                                  let uu____21995 =
                                    let uu____22004 =
                                      let uu____22007 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22007  in
                                    (uu____22004, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21995
                                   in
                                uu____21994 :: quals1  in
                              collect_tcs uu____21991 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22085 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22085 with
                          | (env2,uu____22142,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22279 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22279 with
                          | (env2,uu____22336,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22452 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22498 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22498 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22950  ->
                             match uu___24_22950 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23004,uu____23005);
                                    FStar_Syntax_Syntax.sigrng = uu____23006;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23007;
                                    FStar_Syntax_Syntax.sigmeta = uu____23008;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23009;
                                    FStar_Syntax_Syntax.sigopts = uu____23010;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23072 =
                                     typars_of_binders env1 binders  in
                                   match uu____23072 with
                                   | (env2,tpars1) ->
                                       let uu____23099 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23099 with
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
                                 let uu____23128 =
                                   let uu____23139 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23139)  in
                                 [uu____23128]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23175);
                                    FStar_Syntax_Syntax.sigrng = uu____23176;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23178;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23179;
                                    FStar_Syntax_Syntax.sigopts = uu____23180;_},constrs,tconstr,quals1)
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
                                 let uu____23271 = push_tparams env1 tpars
                                    in
                                 (match uu____23271 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23330  ->
                                             match uu____23330 with
                                             | (x,uu____23342) ->
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
                                        let uu____23353 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23353
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23376 =
                                        let uu____23395 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23472  ->
                                                  match uu____23472 with
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
                                                        let uu____23515 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23515
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
                                                                uu___23_23526
                                                                 ->
                                                                match uu___23_23526
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23538
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23546 =
                                                        let uu____23557 =
                                                          let uu____23558 =
                                                            let uu____23559 =
                                                              let uu____23575
                                                                =
                                                                let uu____23576
                                                                  =
                                                                  let uu____23579
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23579
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23576
                                                                 in
                                                              (name, univs1,
                                                                uu____23575,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23559
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23558;
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
                                                        (tps, uu____23557)
                                                         in
                                                      (name, uu____23546)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23395
                                         in
                                      (match uu____23376 with
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
                             | uu____23711 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23792  ->
                             match uu____23792 with | (uu____23803,se) -> se))
                      in
                   let uu____23817 =
                     let uu____23824 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23824 rng
                      in
                   (match uu____23817 with
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
                               (fun uu____23869  ->
                                  match uu____23869 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23917,tps,k,uu____23920,constrs)
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
                                      let uu____23941 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23956 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23973,uu____23974,uu____23975,uu____23976,uu____23977)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23984
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23956
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23988 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_23995  ->
                                                          match uu___25_23995
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23997 ->
                                                              true
                                                          | uu____24007 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23988))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23941
                                  | uu____24009 -> []))
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
      let uu____24046 =
        FStar_List.fold_left
          (fun uu____24081  ->
             fun b  ->
               match uu____24081 with
               | (env1,binders1) ->
                   let uu____24125 = desugar_binder env1 b  in
                   (match uu____24125 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24148 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24148 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24201 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24046 with
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
          let uu____24305 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24312  ->
                    match uu___26_24312 with
                    | FStar_Syntax_Syntax.Reflectable uu____24314 -> true
                    | uu____24316 -> false))
             in
          if uu____24305
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24321 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24321
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
        let warn1 uu____24372 =
          if warn
          then
            let uu____24374 =
              let uu____24380 =
                let uu____24382 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24382
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24380)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24374
          else ()  in
        let uu____24388 = FStar_Syntax_Util.head_and_args at  in
        match uu____24388 with
        | (hd1,args) ->
            let uu____24441 =
              let uu____24442 = FStar_Syntax_Subst.compress hd1  in
              uu____24442.FStar_Syntax_Syntax.n  in
            (match uu____24441 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24486)::[] ->
                      let uu____24511 =
                        let uu____24516 =
                          let uu____24525 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24525 a1  in
                        uu____24516 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24511 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24548 =
                             let uu____24554 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24554  in
                           (uu____24548, true)
                       | uu____24569 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24585 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24607 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24724 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24724 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24773 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24773 with | (res1,uu____24795) -> rebind res1 true)
  
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
        | uu____25122 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25180 = get_fail_attr1 warn at  in
             comb uu____25180 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25215 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25215 with
        | FStar_Pervasives_Native.None  ->
            let uu____25218 =
              let uu____25224 =
                let uu____25226 =
                  let uu____25228 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25228 " not found"  in
                Prims.op_Hat "Effect name " uu____25226  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25224)  in
            FStar_Errors.raise_error uu____25218 r
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
                    let uu____25384 = desugar_binders monad_env eff_binders
                       in
                    match uu____25384 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25423 =
                            let uu____25432 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25432  in
                          FStar_List.length uu____25423  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____25450 =
                              let uu____25456 =
                                let uu____25458 =
                                  let uu____25460 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25460
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25458  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25456)
                               in
                            FStar_Errors.raise_error uu____25450
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
                                (uu____25528,uu____25529,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25531,uu____25532,uu____25533))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25548 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25551 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25563 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25563 mandatory_members)
                              eff_decls
                             in
                          match uu____25551 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25582 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25611  ->
                                        fun decl  ->
                                          match uu____25611 with
                                          | (env2,out) ->
                                              let uu____25631 =
                                                desugar_decl env2 decl  in
                                              (match uu____25631 with
                                               | (env3,ses) ->
                                                   let uu____25644 =
                                                     let uu____25647 =
                                                       FStar_List.hd ses  in
                                                     uu____25647 :: out  in
                                                   (env3, uu____25644)))
                                     (env1, []))
                                 in
                              (match uu____25582 with
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
                                                 (uu____25693,uu____25694,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25697,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25698,(def,uu____25700)::
                                                        (cps_type,uu____25702)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25703;
                                                     FStar_Parser_AST.level =
                                                       uu____25704;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25737 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25737 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25769 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25770 =
                                                        let uu____25771 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25771
                                                         in
                                                      let uu____25778 =
                                                        let uu____25779 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25779
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25769;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25770;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25778
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25786,uu____25787,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25790,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25806 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25806 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25838 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25839 =
                                                        let uu____25840 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25840
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25838;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25839;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25847 ->
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
                                       let uu____25866 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25866
                                        in
                                     let uu____25868 =
                                       let uu____25869 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25869
                                        in
                                     ([], uu____25868)  in
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
                                       let uu____25891 =
                                         let uu____25892 =
                                           let uu____25895 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25895
                                            in
                                         let uu____25897 =
                                           let uu____25900 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25900
                                            in
                                         let uu____25902 =
                                           let uu____25905 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25905
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
                                             uu____25892;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25897;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25902
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25891
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25939 =
                                            match uu____25939 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25986 =
                                            let uu____25987 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25989 =
                                              let uu____25994 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25994 to_comb
                                               in
                                            let uu____26012 =
                                              let uu____26017 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____26017 to_comb
                                               in
                                            let uu____26035 =
                                              let uu____26040 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____26040 to_comb
                                               in
                                            let uu____26058 =
                                              let uu____26063 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26063 to_comb
                                               in
                                            let uu____26081 =
                                              let uu____26086 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26086 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25987;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25989;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26012;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26035;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26058;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26081
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25986)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26109  ->
                                                 match uu___27_26109 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26112 -> true
                                                 | uu____26114 -> false)
                                              qualifiers
                                             in
                                          let uu____26116 =
                                            let uu____26117 =
                                              lookup1 "return_wp"  in
                                            let uu____26119 =
                                              lookup1 "bind_wp"  in
                                            let uu____26121 =
                                              lookup1 "stronger"  in
                                            let uu____26123 =
                                              lookup1 "if_then_else"  in
                                            let uu____26125 =
                                              lookup1 "ite_wp"  in
                                            let uu____26127 =
                                              lookup1 "close_wp"  in
                                            let uu____26129 =
                                              lookup1 "trivial"  in
                                            let uu____26131 =
                                              if rr
                                              then
                                                let uu____26137 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26137
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26141 =
                                              if rr
                                              then
                                                let uu____26147 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26147
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26151 =
                                              if rr
                                              then
                                                let uu____26157 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26157
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26117;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26119;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26121;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26123;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26125;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26127;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26129;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26131;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26141;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26151
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26116)
                                      in
                                   let sigel =
                                     let uu____26162 =
                                       let uu____26163 =
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
                                           uu____26163
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26162
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
                                               let uu____26180 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26180) env3)
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
                let uu____26203 = desugar_binders env1 eff_binders  in
                match uu____26203 with
                | (env2,binders) ->
                    let uu____26240 =
                      let uu____26251 = head_and_args defn  in
                      match uu____26251 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26288 ->
                                let uu____26289 =
                                  let uu____26295 =
                                    let uu____26297 =
                                      let uu____26299 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____26299 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26297  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26295)
                                   in
                                FStar_Errors.raise_error uu____26289
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26305 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26335)::args_rev ->
                                let uu____26347 =
                                  let uu____26348 = unparen last_arg  in
                                  uu____26348.FStar_Parser_AST.tm  in
                                (match uu____26347 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26376 -> ([], args))
                            | uu____26385 -> ([], args)  in
                          (match uu____26305 with
                           | (cattributes,args1) ->
                               let uu____26428 = desugar_args env2 args1  in
                               let uu____26429 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26428, uu____26429))
                       in
                    (match uu____26240 with
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
                          (let uu____26469 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26469 with
                           | (ed_binders,uu____26483,ed_binders_opening) ->
                               let sub' shift_n uu____26502 =
                                 match uu____26502 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26517 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26517 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26521 =
                                       let uu____26522 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26522)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26521
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26543 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26544 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26545 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26561 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26562 =
                                          let uu____26563 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26563
                                           in
                                        let uu____26578 =
                                          let uu____26579 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26579
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26561;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26562;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26578
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
                                     uu____26543;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26544;
                                   FStar_Syntax_Syntax.actions = uu____26545;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26595 =
                                   let uu____26598 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26598 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26595;
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
                                           let uu____26613 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26613) env3)
                                  in
                               let env5 =
                                 let uu____26615 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26615
                                 then
                                   let reflect_lid =
                                     let uu____26622 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26622
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
             let uu____26655 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26655) ats
         in
      let env0 =
        let uu____26676 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26676 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26691 =
        let uu____26698 = get_fail_attr false attrs  in
        match uu____26698 with
        | FStar_Pervasives_Native.Some (expected_errs,lax1) ->
            let d1 =
              let uu___3447_26735 = d  in
              {
                FStar_Parser_AST.d = (uu___3447_26735.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3447_26735.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3447_26735.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26736 =
              FStar_Errors.catch_errors
                (fun uu____26754  ->
                   FStar_Options.with_saved_options
                     (fun uu____26760  -> desugar_decl_noattrs env d1))
               in
            (match uu____26736 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3462_26820 = se  in
                             let uu____26821 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3462_26820.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3462_26820.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3462_26820.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3462_26820.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26821;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3462_26820.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____26874 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26874 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____26923 =
                                 let uu____26929 =
                                   let uu____26931 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____26934 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____26937 =
                                     FStar_Util.string_of_int e  in
                                   let uu____26939 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____26941 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____26931 uu____26934 uu____26937
                                     uu____26939 uu____26941
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____26929)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____26923);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26691 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26979;
                FStar_Syntax_Syntax.sigrng = uu____26980;
                FStar_Syntax_Syntax.sigquals = uu____26981;
                FStar_Syntax_Syntax.sigmeta = uu____26982;
                FStar_Syntax_Syntax.sigattrs = uu____26983;
                FStar_Syntax_Syntax.sigopts = uu____26984;_}::[] ->
                let uu____26997 =
                  let uu____27000 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27000  in
                FStar_All.pipe_right uu____26997
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27008 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27008))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27021;
                FStar_Syntax_Syntax.sigrng = uu____27022;
                FStar_Syntax_Syntax.sigquals = uu____27023;
                FStar_Syntax_Syntax.sigmeta = uu____27024;
                FStar_Syntax_Syntax.sigattrs = uu____27025;
                FStar_Syntax_Syntax.sigopts = uu____27026;_}::uu____27027 ->
                let uu____27052 =
                  let uu____27055 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27055  in
                FStar_All.pipe_right uu____27052
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27063 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27063))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27079;
                FStar_Syntax_Syntax.sigquals = uu____27080;
                FStar_Syntax_Syntax.sigmeta = uu____27081;
                FStar_Syntax_Syntax.sigattrs = uu____27082;
                FStar_Syntax_Syntax.sigopts = uu____27083;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27104 -> []  in
          let attrs1 =
            let uu____27110 = val_attrs sigelts  in
            FStar_List.append attrs uu____27110  in
          let uu____27113 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3522_27117 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3522_27117.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3522_27117.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3522_27117.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3522_27117.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3522_27117.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27113)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27124 = desugar_decl_aux env d  in
      match uu____27124 with
      | (env1,ses) ->
          let uu____27135 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27135)

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
          let uu____27167 = FStar_Syntax_DsEnv.iface env  in
          if uu____27167
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27182 =
               let uu____27184 =
                 let uu____27186 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27187 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27186
                   uu____27187
                  in
               Prims.op_Negation uu____27184  in
             if uu____27182
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27201 =
                  let uu____27203 =
                    let uu____27205 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27205 lid  in
                  Prims.op_Negation uu____27203  in
                if uu____27201
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27219 =
                     let uu____27221 =
                       let uu____27223 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27223
                         lid
                        in
                     Prims.op_Negation uu____27221  in
                   if uu____27219
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27241 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27241, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27270)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27289 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27298 =
            let uu____27303 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27303 tcs  in
          (match uu____27298 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27320 =
                   let uu____27321 =
                     let uu____27328 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27328  in
                   [uu____27321]  in
                 let uu____27341 =
                   let uu____27344 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27347 =
                     let uu____27358 =
                       let uu____27367 =
                         let uu____27368 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27368  in
                       FStar_Syntax_Syntax.as_arg uu____27367  in
                     [uu____27358]  in
                   FStar_Syntax_Util.mk_app uu____27344 uu____27347  in
                 FStar_Syntax_Util.abs uu____27320 uu____27341
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27408,id1))::uu____27410 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____27413::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27417 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27417 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____27423 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____27423]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27444) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27454,uu____27455,uu____27456,uu____27457,uu____27458)
                     ->
                     let uu____27467 =
                       let uu____27468 =
                         let uu____27469 =
                           let uu____27476 = mkclass lid  in
                           (meths, uu____27476)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27469  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27468;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27467]
                 | uu____27479 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27513;
                    FStar_Parser_AST.prange = uu____27514;_},uu____27515)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27525;
                    FStar_Parser_AST.prange = uu____27526;_},uu____27527)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27543;
                         FStar_Parser_AST.prange = uu____27544;_},uu____27545);
                    FStar_Parser_AST.prange = uu____27546;_},uu____27547)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27569;
                         FStar_Parser_AST.prange = uu____27570;_},uu____27571);
                    FStar_Parser_AST.prange = uu____27572;_},uu____27573)::[]
                   -> false
               | (p,uu____27602)::[] ->
                   let uu____27611 = is_app_pattern p  in
                   Prims.op_Negation uu____27611
               | uu____27613 -> false)
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
            let uu____27688 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27688 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27701 =
                     let uu____27702 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27702.FStar_Syntax_Syntax.n  in
                   match uu____27701 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27712) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27743 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27768  ->
                                match uu____27768 with
                                | (qs,ats) ->
                                    let uu____27795 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27795 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27743 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27849::uu____27850 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27853 -> val_quals  in
                            let quals2 =
                              let uu____27857 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27890  ->
                                        match uu____27890 with
                                        | (uu____27904,(uu____27905,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27857
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27925 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27925
                              then
                                let uu____27931 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3699_27946 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3701_27948 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3701_27948.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3701_27948.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3699_27946.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27931)
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
                   | uu____27973 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27981 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28000 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27981 with
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
                       let uu___3724_28037 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3724_28037.FStar_Parser_AST.prange)
                       }
                   | uu____28044 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3728_28051 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3728_28051.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3728_28051.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28067 =
                     let uu____28068 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28068  in
                   FStar_Parser_AST.mk_term uu____28067
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28092 id_opt =
                   match uu____28092 with
                   | (env1,ses) ->
                       let uu____28114 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____28126 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28126
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28128 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28128
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
                               let uu____28134 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28134
                                in
                             let bv_pat1 =
                               let uu____28138 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28138
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____28114 with
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
                            let uu____28199 = desugar_decl env1 id_decl  in
                            (match uu____28199 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28235 id1 =
                   match uu____28235 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____28274 =
                   match uu____28274 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28298 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28298 FStar_Util.set_elements
                    in
                 let uu____28305 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28308 = is_var_pattern pat  in
                      Prims.op_Negation uu____28308)
                    in
                 if uu____28305
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
            let uu____28332 = close_fun env t  in
            desugar_term env uu____28332  in
          let quals1 =
            let uu____28336 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28336
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28348 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28348;
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
                let uu____28361 =
                  let uu____28370 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28370]  in
                let uu____28389 =
                  let uu____28392 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28392
                   in
                FStar_Syntax_Util.arrow uu____28361 uu____28389
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
          let uu____28458 =
            let uu____28460 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28460  in
          if uu____28458
          then
            let uu____28467 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28485 =
                    let uu____28488 =
                      let uu____28489 = desugar_term env t  in
                      ([], uu____28489)  in
                    FStar_Pervasives_Native.Some uu____28488  in
                  (uu____28485, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28502 =
                    let uu____28505 =
                      let uu____28506 = desugar_term env wp  in
                      ([], uu____28506)  in
                    FStar_Pervasives_Native.Some uu____28505  in
                  let uu____28513 =
                    let uu____28516 =
                      let uu____28517 = desugar_term env t  in
                      ([], uu____28517)  in
                    FStar_Pervasives_Native.Some uu____28516  in
                  (uu____28502, uu____28513)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28529 =
                    let uu____28532 =
                      let uu____28533 = desugar_term env t  in
                      ([], uu____28533)  in
                    FStar_Pervasives_Native.Some uu____28532  in
                  (FStar_Pervasives_Native.None, uu____28529)
               in
            (match uu____28467 with
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
                   let uu____28567 =
                     let uu____28570 =
                       let uu____28571 = desugar_term env t  in
                       ([], uu____28571)  in
                     FStar_Pervasives_Native.Some uu____28570  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28567
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
             | uu____28578 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28591 =
            let uu____28592 =
              let uu____28593 =
                let uu____28594 =
                  let uu____28605 =
                    let uu____28606 = desugar_term env bind1  in
                    ([], uu____28606)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28605,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28594  in
              {
                FStar_Syntax_Syntax.sigel = uu____28593;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28592]  in
          (env, uu____28591)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28625 =
              let uu____28626 =
                let uu____28633 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28633, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28626  in
            {
              FStar_Syntax_Syntax.sigel = uu____28625;
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
      let uu____28660 =
        FStar_List.fold_left
          (fun uu____28680  ->
             fun d  ->
               match uu____28680 with
               | (env1,sigelts) ->
                   let uu____28700 = desugar_decl env1 d  in
                   (match uu____28700 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28660 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28791) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28795;
               FStar_Syntax_Syntax.exports = uu____28796;
               FStar_Syntax_Syntax.is_interface = uu____28797;_},FStar_Parser_AST.Module
             (current_lid,uu____28799)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28808) ->
              let uu____28811 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28811
           in
        let uu____28816 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28858 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28858, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28880 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28880, mname, decls, false)
           in
        match uu____28816 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28922 = desugar_decls env2 decls  in
            (match uu____28922 with
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
          let uu____28990 =
            (FStar_Options.interactive ()) &&
              (let uu____28993 =
                 let uu____28995 =
                   let uu____28997 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28997  in
                 FStar_Util.get_file_extension uu____28995  in
               FStar_List.mem uu____28993 ["fsti"; "fsi"])
             in
          if uu____28990 then as_interface m else m  in
        let uu____29011 = desugar_modul_common curmod env m1  in
        match uu____29011 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29033 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29033, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29055 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29055 with
      | (env1,modul,pop_when_done) ->
          let uu____29072 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29072 with
           | (env2,modul1) ->
               ((let uu____29084 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____29084
                 then
                   let uu____29087 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29087
                 else ());
                (let uu____29092 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29092, modul1))))
  
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
        (fun uu____29142  ->
           let uu____29143 = desugar_modul env modul  in
           match uu____29143 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29181  ->
           let uu____29182 = desugar_decls env decls  in
           match uu____29182 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29233  ->
             let uu____29234 = desugar_partial_modul modul env a_modul  in
             match uu____29234 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29329 ->
                  let t =
                    let uu____29339 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29339  in
                  let uu____29352 =
                    let uu____29353 = FStar_Syntax_Subst.compress t  in
                    uu____29353.FStar_Syntax_Syntax.n  in
                  (match uu____29352 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29365,uu____29366)
                       -> bs1
                   | uu____29391 -> failwith "Impossible")
               in
            let uu____29401 =
              let uu____29408 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29408
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29401 with
            | (binders,uu____29410,binders_opening) ->
                let erase_term t =
                  let uu____29418 =
                    let uu____29419 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29419  in
                  FStar_Syntax_Subst.close binders uu____29418  in
                let erase_tscheme uu____29437 =
                  match uu____29437 with
                  | (us,t) ->
                      let t1 =
                        let uu____29457 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29457 t  in
                      let uu____29460 =
                        let uu____29461 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29461  in
                      ([], uu____29460)
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
                    | uu____29484 ->
                        let bs =
                          let uu____29494 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29494  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29534 =
                          let uu____29535 =
                            let uu____29538 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29538  in
                          uu____29535.FStar_Syntax_Syntax.n  in
                        (match uu____29534 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29540,uu____29541) -> bs1
                         | uu____29566 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29574 =
                      let uu____29575 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29575  in
                    FStar_Syntax_Subst.close binders uu____29574  in
                  let uu___4021_29576 = action  in
                  let uu____29577 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29578 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4021_29576.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4021_29576.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29577;
                    FStar_Syntax_Syntax.action_typ = uu____29578
                  }  in
                let uu___4023_29579 = ed  in
                let uu____29580 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29581 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29582 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29583 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___4023_29579.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4023_29579.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29580;
                  FStar_Syntax_Syntax.signature = uu____29581;
                  FStar_Syntax_Syntax.combinators = uu____29582;
                  FStar_Syntax_Syntax.actions = uu____29583;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4023_29579.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4030_29599 = se  in
                  let uu____29600 =
                    let uu____29601 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29601  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29600;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4030_29599.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4030_29599.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4030_29599.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4030_29599.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4030_29599.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29603 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29604 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29604 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29621 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____29621
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29623 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29623)
  