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
        let uu____712 =
          let uu____713 =
            let uu____714 =
              let uu____720 = FStar_Parser_AST.compile_op n s r  in
              (uu____720, r)  in
            FStar_Ident.mk_ident uu____714  in
          [uu____713]  in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
  
let op_as_term :
  'uuuuuu734 .
    env_t ->
      Prims.int ->
        'uuuuuu734 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____772 =
              let uu____773 =
                let uu____774 =
                  let uu____775 = FStar_Ident.range_of_id op  in
                  FStar_Ident.set_lid_range l uu____775  in
                FStar_Syntax_Syntax.lid_as_fv uu____774 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____773 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____772  in
          let fallback uu____783 =
            let uu____784 = FStar_Ident.text_of_id op  in
            match uu____784 with
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
                let uu____805 = FStar_Options.ml_ish ()  in
                if uu____805
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
            | uu____830 -> FStar_Pervasives_Native.None  in
          let uu____832 =
            let uu____835 =
              let uu____836 = FStar_Ident.text_of_id op  in
              let uu____838 = FStar_Ident.range_of_id op  in
              compile_op_lid arity uu____836 uu____838  in
            desugar_name'
              (fun t  ->
                 let uu___202_846 = t  in
                 let uu____847 = FStar_Ident.range_of_id op  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___202_846.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = uu____847;
                   FStar_Syntax_Syntax.vars =
                     (uu___202_846.FStar_Syntax_Syntax.vars)
                 }) env true uu____835
             in
          match uu____832 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____852 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____867 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____876 = FStar_Ident.text_of_id x  in
             let uu____878 = FStar_Ident.text_of_id y  in
             uu____876 = uu____878) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____891 = FStar_Ident.text_of_id x  in
              let uu____893 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____891 uu____893)) uu____867
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____928 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____932 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____932 with | (env1,uu____944) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____947,term) ->
          let uu____949 = free_type_vars env term  in (env, uu____949)
      | FStar_Parser_AST.TAnnotated (id,uu____955) ->
          let uu____956 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____956 with | (env1,uu____968) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____972 = free_type_vars env t  in (env, uu____972)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____979 =
        let uu____980 = unparen t  in uu____980.FStar_Parser_AST.tm  in
      match uu____979 with
      | FStar_Parser_AST.Labeled uu____983 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____996 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____996 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____1001 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____1004 -> []
      | FStar_Parser_AST.Uvar uu____1005 -> []
      | FStar_Parser_AST.Var uu____1006 -> []
      | FStar_Parser_AST.Projector uu____1007 -> []
      | FStar_Parser_AST.Discrim uu____1012 -> []
      | FStar_Parser_AST.Name uu____1013 -> []
      | FStar_Parser_AST.Requires (t1,uu____1015) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1023) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1030,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1049,ts) ->
          FStar_List.collect
            (fun uu____1070  ->
               match uu____1070 with
               | (t1,uu____1078) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1079,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1087) ->
          let uu____1088 = free_type_vars env t1  in
          let uu____1091 = free_type_vars env t2  in
          FStar_List.append uu____1088 uu____1091
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1096 = free_type_vars_b env b  in
          (match uu____1096 with
           | (env1,f) ->
               let uu____1111 = free_type_vars env1 t1  in
               FStar_List.append f uu____1111)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1128 =
            FStar_List.fold_left
              (fun uu____1152  ->
                 fun bt  ->
                   match uu____1152 with
                   | (env1,free) ->
                       let uu____1176 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1191 = free_type_vars env1 body  in
                             (env1, uu____1191)
                          in
                       (match uu____1176 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1128 with
           | (env1,free) ->
               let uu____1220 = free_type_vars env1 body  in
               FStar_List.append free uu____1220)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1229 =
            FStar_List.fold_left
              (fun uu____1249  ->
                 fun binder  ->
                   match uu____1249 with
                   | (env1,free) ->
                       let uu____1269 = free_type_vars_b env1 binder  in
                       (match uu____1269 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1229 with
           | (env1,free) ->
               let uu____1300 = free_type_vars env1 body  in
               FStar_List.append free uu____1300)
      | FStar_Parser_AST.Project (t1,uu____1304) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1315 = free_type_vars env rel  in
          let uu____1318 =
            let uu____1321 = free_type_vars env init  in
            let uu____1324 =
              FStar_List.collect
                (fun uu____1333  ->
                   match uu____1333 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1339 = free_type_vars env rel1  in
                       let uu____1342 =
                         let uu____1345 = free_type_vars env just  in
                         let uu____1348 = free_type_vars env next  in
                         FStar_List.append uu____1345 uu____1348  in
                       FStar_List.append uu____1339 uu____1342) steps
               in
            FStar_List.append uu____1321 uu____1324  in
          FStar_List.append uu____1315 uu____1318
      | FStar_Parser_AST.Abs uu____1351 -> []
      | FStar_Parser_AST.Let uu____1358 -> []
      | FStar_Parser_AST.LetOpen uu____1379 -> []
      | FStar_Parser_AST.If uu____1384 -> []
      | FStar_Parser_AST.QForall uu____1391 -> []
      | FStar_Parser_AST.QExists uu____1410 -> []
      | FStar_Parser_AST.Record uu____1429 -> []
      | FStar_Parser_AST.Match uu____1442 -> []
      | FStar_Parser_AST.TryWith uu____1457 -> []
      | FStar_Parser_AST.Bind uu____1472 -> []
      | FStar_Parser_AST.Quote uu____1479 -> []
      | FStar_Parser_AST.VQuote uu____1484 -> []
      | FStar_Parser_AST.Antiquote uu____1485 -> []
      | FStar_Parser_AST.Seq uu____1486 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1540 =
        let uu____1541 = unparen t1  in uu____1541.FStar_Parser_AST.tm  in
      match uu____1540 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1583 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1608 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1608  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1631 =
                     let uu____1632 =
                       let uu____1637 =
                         let uu____1638 = FStar_Ident.range_of_id x  in
                         tm_type uu____1638  in
                       (x, uu____1637)  in
                     FStar_Parser_AST.TAnnotated uu____1632  in
                   let uu____1639 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1631 uu____1639
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
        let uu____1657 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1657  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1680 =
                     let uu____1681 =
                       let uu____1686 =
                         let uu____1687 = FStar_Ident.range_of_id x  in
                         tm_type uu____1687  in
                       (x, uu____1686)  in
                     FStar_Parser_AST.TAnnotated uu____1681  in
                   let uu____1688 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1680 uu____1688
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1690 =
             let uu____1691 = unparen t  in uu____1691.FStar_Parser_AST.tm
              in
           match uu____1690 with
           | FStar_Parser_AST.Product uu____1692 -> t
           | uu____1699 ->
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
      | uu____1736 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1747 -> true
    | FStar_Parser_AST.PatTvar (uu____1751,uu____1752) -> true
    | FStar_Parser_AST.PatVar (uu____1758,uu____1759) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1766) -> is_var_pattern p1
    | uu____1779 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1790) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1803;
           FStar_Parser_AST.prange = uu____1804;_},uu____1805)
        -> true
    | uu____1817 -> false
  
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
    | uu____1833 -> p
  
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
            let uu____1906 = destruct_app_pattern env is_top_level p1  in
            (match uu____1906 with
             | (name,args,uu____1949) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1999);
               FStar_Parser_AST.prange = uu____2000;_},args)
            when is_top_level ->
            let uu____2010 =
              let uu____2015 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____2015  in
            (uu____2010, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____2037);
               FStar_Parser_AST.prange = uu____2038;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____2068 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2120 -> acc
      | FStar_Parser_AST.PatConst uu____2123 -> acc
      | FStar_Parser_AST.PatName uu____2124 -> acc
      | FStar_Parser_AST.PatOp uu____2125 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2133) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2139) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2148) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2165 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2165
      | FStar_Parser_AST.PatAscribed (pat,uu____2173) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2201 =
             let uu____2203 = FStar_Ident.text_of_id id1  in
             let uu____2205 = FStar_Ident.text_of_id id2  in
             uu____2203 = uu____2205  in
           if uu____2201 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2253 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2294 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2342,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2343))
        -> true
    | uu____2346 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2357  ->
    match uu___3_2357 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2364 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2397  ->
    match uu____2397 with
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
      let uu____2479 =
        let uu____2496 =
          let uu____2499 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2499  in
        let uu____2500 =
          let uu____2511 =
            let uu____2520 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2520)  in
          [uu____2511]  in
        (uu____2496, uu____2500)  in
      FStar_Syntax_Syntax.Tm_app uu____2479  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2569 =
        let uu____2586 =
          let uu____2589 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2589  in
        let uu____2590 =
          let uu____2601 =
            let uu____2610 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2610)  in
          [uu____2601]  in
        (uu____2586, uu____2590)  in
      FStar_Syntax_Syntax.Tm_app uu____2569  in
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
          let uu____2673 =
            let uu____2690 =
              let uu____2693 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2693  in
            let uu____2694 =
              let uu____2705 =
                let uu____2714 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2714)  in
              let uu____2722 =
                let uu____2733 =
                  let uu____2742 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2742)  in
                [uu____2733]  in
              uu____2705 :: uu____2722  in
            (uu____2690, uu____2694)  in
          FStar_Syntax_Syntax.Tm_app uu____2673  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2802 =
        let uu____2817 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2836  ->
               match uu____2836 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2847;
                    FStar_Syntax_Syntax.index = uu____2848;
                    FStar_Syntax_Syntax.sort = t;_},uu____2850)
                   ->
                   let uu____2858 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2858) uu____2817
         in
      FStar_All.pipe_right bs uu____2802  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2874 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2892 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2920 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2941,uu____2942,bs,t,uu____2945,uu____2946)
                            ->
                            let uu____2955 = bs_univnames bs  in
                            let uu____2958 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2955 uu____2958
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2961,uu____2962,t,uu____2964,uu____2965,uu____2966)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2973 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2920 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___589_2982 = s  in
        let uu____2983 =
          let uu____2984 =
            let uu____2993 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3011,bs,t,lids1,lids2) ->
                          let uu___600_3024 = se  in
                          let uu____3025 =
                            let uu____3026 =
                              let uu____3043 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3044 =
                                let uu____3045 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3045 t  in
                              (lid, uvs, uu____3043, uu____3044, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3026
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3025;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___600_3024.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___600_3024.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___600_3024.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___600_3024.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___600_3024.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3059,t,tlid,n,lids1) ->
                          let uu___610_3070 = se  in
                          let uu____3071 =
                            let uu____3072 =
                              let uu____3088 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3088, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3072  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3071;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___610_3070.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___610_3070.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___610_3070.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___610_3070.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___610_3070.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3092 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2993, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2984  in
        {
          FStar_Syntax_Syntax.sigel = uu____2983;
          FStar_Syntax_Syntax.sigrng =
            (uu___589_2982.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___589_2982.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___589_2982.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___589_2982.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___589_2982.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3099,t) ->
        let uvs =
          let uu____3102 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3102 FStar_Util.set_elements  in
        let uu___619_3107 = s  in
        let uu____3108 =
          let uu____3109 =
            let uu____3116 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3116)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3109  in
        {
          FStar_Syntax_Syntax.sigel = uu____3108;
          FStar_Syntax_Syntax.sigrng =
            (uu___619_3107.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___619_3107.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___619_3107.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___619_3107.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___619_3107.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3140 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3143 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3150) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3183,(FStar_Util.Inl t,uu____3185),uu____3186)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3233,(FStar_Util.Inr c,uu____3235),uu____3236)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3283 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3285) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3306,(FStar_Util.Inl t,uu____3308),uu____3309) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3356,(FStar_Util.Inr c,uu____3358),uu____3359) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3406 -> empty_set  in
          FStar_Util.set_union uu____3140 uu____3143  in
        let all_lb_univs =
          let uu____3410 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3426 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3426) empty_set)
             in
          FStar_All.pipe_right uu____3410 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___678_3436 = s  in
        let uu____3437 =
          let uu____3438 =
            let uu____3445 =
              let uu____3446 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___681_3458 = lb  in
                        let uu____3459 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3462 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___681_3458.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3459;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___681_3458.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3462;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___681_3458.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___681_3458.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3446)  in
            (uu____3445, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3438  in
        {
          FStar_Syntax_Syntax.sigel = uu____3437;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3436.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3436.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3436.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3436.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3436.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3471,fml) ->
        let uvs =
          let uu____3474 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3474 FStar_Util.set_elements  in
        let uu___689_3479 = s  in
        let uu____3480 =
          let uu____3481 =
            let uu____3488 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3488)  in
          FStar_Syntax_Syntax.Sig_assume uu____3481  in
        {
          FStar_Syntax_Syntax.sigel = uu____3480;
          FStar_Syntax_Syntax.sigrng =
            (uu___689_3479.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___689_3479.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___689_3479.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___689_3479.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___689_3479.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3490,bs,c,flags) ->
        let uvs =
          let uu____3499 =
            let uu____3502 = bs_univnames bs  in
            let uu____3505 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3502 uu____3505  in
          FStar_All.pipe_right uu____3499 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___700_3513 = s  in
        let uu____3514 =
          let uu____3515 =
            let uu____3528 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3529 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3528, uu____3529, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3515  in
        {
          FStar_Syntax_Syntax.sigel = uu____3514;
          FStar_Syntax_Syntax.sigrng =
            (uu___700_3513.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___700_3513.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___700_3513.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___700_3513.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___700_3513.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___707_3547 = s  in
        let uu____3548 =
          let uu____3549 =
            let uu____3562 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3562)  in
          FStar_Syntax_Syntax.Sig_fail uu____3549  in
        {
          FStar_Syntax_Syntax.sigel = uu____3548;
          FStar_Syntax_Syntax.sigrng =
            (uu___707_3547.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___707_3547.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___707_3547.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___707_3547.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___707_3547.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3571 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3572 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3573 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3574 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3585 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3592 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3600  ->
    match uu___4_3600 with
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
    | uu____3649 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3670 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3670)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3696 =
      let uu____3697 = unparen t  in uu____3697.FStar_Parser_AST.tm  in
    match uu____3696 with
    | FStar_Parser_AST.Wild  ->
        let uu____3703 =
          let uu____3704 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3704  in
        FStar_Util.Inr uu____3703
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3717)) ->
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
             let uu____3808 = sum_to_universe u n  in
             FStar_Util.Inr uu____3808
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3825 = sum_to_universe u n  in
             FStar_Util.Inr uu____3825
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3841 =
               let uu____3847 =
                 let uu____3849 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3849
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3847)
                in
             FStar_Errors.raise_error uu____3841 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3858 ->
        let rec aux t1 univargs =
          let uu____3895 =
            let uu____3896 = unparen t1  in uu____3896.FStar_Parser_AST.tm
             in
          match uu____3895 with
          | FStar_Parser_AST.App (t2,targ,uu____3904) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3931  ->
                     match uu___5_3931 with
                     | FStar_Util.Inr uu____3938 -> true
                     | uu____3941 -> false) univargs
              then
                let uu____3949 =
                  let uu____3950 =
                    FStar_List.map
                      (fun uu___6_3960  ->
                         match uu___6_3960 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3950  in
                FStar_Util.Inr uu____3949
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3986  ->
                        match uu___7_3986 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3996 -> failwith "impossible")
                     univargs
                    in
                 let uu____4000 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____4000)
          | uu____4016 ->
              let uu____4017 =
                let uu____4023 =
                  let uu____4025 =
                    let uu____4027 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4027 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4025  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4023)  in
              FStar_Errors.raise_error uu____4017 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4042 ->
        let uu____4043 =
          let uu____4049 =
            let uu____4051 =
              let uu____4053 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4053 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4051  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4049)  in
        FStar_Errors.raise_error uu____4043 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4094;_});
            FStar_Syntax_Syntax.pos = uu____4095;
            FStar_Syntax_Syntax.vars = uu____4096;_})::uu____4097
        ->
        let uu____4128 =
          let uu____4134 =
            let uu____4136 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4136
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4134)  in
        FStar_Errors.raise_error uu____4128 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4142 ->
        let uu____4161 =
          let uu____4167 =
            let uu____4169 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4169
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4167)  in
        FStar_Errors.raise_error uu____4161 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4182 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4182) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4210 = FStar_List.hd fields  in
        match uu____4210 with
        | (f,uu____4220) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4231 =
              match uu____4231 with
              | (f',uu____4237) ->
                  let uu____4238 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4238
                  then ()
                  else
                    (let msg =
                       let uu____4245 = FStar_Ident.string_of_lid f  in
                       let uu____4247 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4249 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4245 uu____4247 uu____4249
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4254 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4254);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4302 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4309 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4310 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4312,pats1) ->
            let aux out uu____4353 =
              match uu____4353 with
              | (p1,uu____4366) ->
                  let intersection =
                    let uu____4376 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4376 out  in
                  let uu____4379 = FStar_Util.set_is_empty intersection  in
                  if uu____4379
                  then
                    let uu____4384 = pat_vars p1  in
                    FStar_Util.set_union out uu____4384
                  else
                    (let duplicate_bv =
                       let uu____4390 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4390  in
                     let uu____4393 =
                       let uu____4399 =
                         let uu____4401 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4401
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4399)
                        in
                     FStar_Errors.raise_error uu____4393 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4425 = pat_vars p  in
          FStar_All.pipe_right uu____4425 (fun uu____4430  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4454 =
              let uu____4456 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4456  in
            if uu____4454
            then ()
            else
              (let nonlinear_vars =
                 let uu____4465 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4465  in
               let first_nonlinear_var =
                 let uu____4469 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4469  in
               let uu____4472 =
                 let uu____4478 =
                   let uu____4480 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4480
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4478)  in
               FStar_Errors.raise_error uu____4472 r)
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
          let uu____4807 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4814 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4816 = FStar_Ident.text_of_id x  in
                 uu____4814 = uu____4816) l
             in
          match uu____4807 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4830 ->
              let uu____4833 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4833 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4974 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4996 =
                  let uu____5002 =
                    let uu____5004 = FStar_Ident.text_of_id op  in
                    let uu____5006 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____5004
                      uu____5006
                     in
                  let uu____5008 = FStar_Ident.range_of_id op  in
                  (uu____5002, uu____5008)  in
                FStar_Ident.mk_ident uu____4996  in
              let p2 =
                let uu___934_5011 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_5011.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5028 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5031 = aux loc env1 p2  in
                match uu____5031 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5087 =
                      match binder with
                      | LetBinder uu____5108 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5133 = close_fun env1 t  in
                            desugar_term env1 uu____5133  in
                          let x1 =
                            let uu___960_5135 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5135.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5135.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5087 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5181 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5182 -> ()
                           | uu____5183 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5184 ->
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
              let uu____5202 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5202, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5215 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5215, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5233 = resolvex loc env1 x  in
              (match uu____5233 with
               | (loc1,env2,xbv) ->
                   let uu____5265 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5265, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5283 = resolvex loc env1 x  in
              (match uu____5283 with
               | (loc1,env2,xbv) ->
                   let uu____5315 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5315, []))
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
              let uu____5329 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5329, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5357;_},args)
              ->
              let uu____5363 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5424  ->
                       match uu____5424 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5505 = aux loc1 env2 arg  in
                           (match uu____5505 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5363 with
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
                   let uu____5677 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5677, annots))
          | FStar_Parser_AST.PatApp uu____5693 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5721 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5771  ->
                       match uu____5771 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5832 = aux loc1 env2 pat  in
                           (match uu____5832 with
                            | (loc2,env3,uu____5871,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5721 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5965 =
                       let uu____5968 =
                         let uu____5975 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5975  in
                       let uu____5976 =
                         let uu____5977 =
                           let uu____5991 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5991, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5977  in
                       FStar_All.pipe_left uu____5968 uu____5976  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6025 =
                              let uu____6026 =
                                let uu____6040 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6040, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6026  in
                            FStar_All.pipe_left (pos_r r) uu____6025) pats1
                       uu____5965
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
              let uu____6096 =
                FStar_List.fold_left
                  (fun uu____6155  ->
                     fun p2  ->
                       match uu____6155 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6237 = aux loc1 env2 p2  in
                           (match uu____6237 with
                            | (loc2,env3,uu____6281,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6096 with
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
                     | uu____6444 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6447 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6447, annots))
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
                     (fun uu____6524  ->
                        match uu____6524 with
                        | (f,p2) ->
                            let uu____6535 = FStar_Ident.ident_of_lid f  in
                            (uu____6535, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6555  ->
                        match uu____6555 with
                        | (f,uu____6561) ->
                            let uu____6562 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6590  ->
                                      match uu____6590 with
                                      | (g,uu____6597) ->
                                          let uu____6598 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6600 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6598 = uu____6600))
                               in
                            (match uu____6562 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6607,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6614 =
                  let uu____6615 =
                    let uu____6622 =
                      let uu____6623 =
                        let uu____6624 =
                          let uu____6625 =
                            let uu____6626 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6626
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6625  in
                        FStar_Parser_AST.PatName uu____6624  in
                      FStar_Parser_AST.mk_pattern uu____6623
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6622, args)  in
                  FStar_Parser_AST.PatApp uu____6615  in
                FStar_Parser_AST.mk_pattern uu____6614
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6631 = aux loc env1 app  in
              (match uu____6631 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6708 =
                           let uu____6709 =
                             let uu____6723 =
                               let uu___1110_6724 = fv  in
                               let uu____6725 =
                                 let uu____6728 =
                                   let uu____6729 =
                                     let uu____6736 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6736)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6729
                                    in
                                 FStar_Pervasives_Native.Some uu____6728  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6724.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6724.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6725
                               }  in
                             (uu____6723, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6709  in
                         FStar_All.pipe_left pos uu____6708
                     | uu____6762 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6846 = aux' true loc env1 p2  in
              (match uu____6846 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6899 =
                     FStar_List.fold_left
                       (fun uu____6947  ->
                          fun p4  ->
                            match uu____6947 with
                            | (loc2,env3,ps1) ->
                                let uu____7012 = aux' true loc2 env3 p4  in
                                (match uu____7012 with
                                 | (loc3,env4,uu____7050,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6899 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7211 ->
              let uu____7212 = aux' true loc env1 p1  in
              (match uu____7212 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7303 = aux_maybe_or env p  in
        match uu____7303 with
        | (env1,b,pats) ->
            ((let uu____7358 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7358
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
            let uu____7432 =
              let uu____7433 =
                let uu____7444 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7444, (ty, tacopt))  in
              LetBinder uu____7433  in
            (env, uu____7432, [])  in
          let op_to_ident x =
            let uu____7461 =
              let uu____7467 =
                let uu____7469 = FStar_Ident.text_of_id x  in
                let uu____7471 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7469
                  uu____7471
                 in
              let uu____7473 = FStar_Ident.range_of_id x  in
              (uu____7467, uu____7473)  in
            FStar_Ident.mk_ident uu____7461  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7484 = op_to_ident x  in
              mklet uu____7484 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7486) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7492;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7508 = op_to_ident x  in
              let uu____7509 = desugar_term env t  in
              mklet uu____7508 uu____7509 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7511);
                 FStar_Parser_AST.prange = uu____7512;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7532 = desugar_term env t  in
              mklet x uu____7532 tacopt1
          | uu____7533 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7546 = desugar_data_pat true env p  in
           match uu____7546 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7576;
                      FStar_Syntax_Syntax.p = uu____7577;_},uu____7578)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7591;
                      FStar_Syntax_Syntax.p = uu____7592;_},uu____7593)::[]
                     -> []
                 | uu____7606 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7614  ->
    fun env  ->
      fun pat  ->
        let uu____7618 = desugar_data_pat false env pat  in
        match uu____7618 with | (env1,uu____7635,pat1) -> (env1, pat1)

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
      let uu____7657 = desugar_term_aq env e  in
      match uu____7657 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7676 = desugar_typ_aq env e  in
      match uu____7676 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7686  ->
        fun range  ->
          match uu____7686 with
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
              ((let uu____7708 =
                  let uu____7710 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7710  in
                if uu____7708
                then
                  let uu____7713 =
                    let uu____7719 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7719)  in
                  FStar_Errors.log_issue range uu____7713
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
                  let uu____7740 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7740 range  in
                let lid1 =
                  let uu____7744 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7744 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7754 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7754 range  in
                           let private_fv =
                             let uu____7756 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7756 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7757 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7757.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7757.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7758 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7762 =
                        let uu____7768 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7768)
                         in
                      FStar_Errors.raise_error uu____7762 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7788 =
                  let uu____7795 =
                    let uu____7796 =
                      let uu____7813 =
                        let uu____7824 =
                          let uu____7833 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7833)  in
                        [uu____7824]  in
                      (lid1, uu____7813)  in
                    FStar_Syntax_Syntax.Tm_app uu____7796  in
                  FStar_Syntax_Syntax.mk uu____7795  in
                uu____7788 FStar_Pervasives_Native.None range))

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
          let uu___1293_7952 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7952.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7952.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7955 =
          let uu____7956 = unparen top  in uu____7956.FStar_Parser_AST.tm  in
        match uu____7955 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7961 ->
            let uu____7970 = desugar_formula env top  in (uu____7970, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7979 = desugar_formula env t  in (uu____7979, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7988 = desugar_formula env t  in (uu____7988, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8015 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8015, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8017 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8017, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8024 = FStar_Ident.text_of_id id  in uu____8024 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8030 =
                let uu____8031 =
                  let uu____8038 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8038, args)  in
                FStar_Parser_AST.Op uu____8031  in
              FStar_Parser_AST.mk_term uu____8030 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8043 =
              let uu____8044 =
                let uu____8045 =
                  let uu____8052 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8052, [e])  in
                FStar_Parser_AST.Op uu____8045  in
              FStar_Parser_AST.mk_term uu____8044 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8043
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8064 = FStar_Ident.text_of_id op_star  in
             uu____8064 = "*") &&
              (let uu____8069 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8069 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8093 = FStar_Ident.text_of_id id  in
                   uu____8093 = "*") &&
                    (let uu____8098 =
                       op_as_term env (Prims.of_int (2))
                         top.FStar_Parser_AST.range op_star
                        in
                     FStar_All.pipe_right uu____8098 FStar_Option.isNone)
                  ->
                  let uu____8105 = flatten t1  in
                  FStar_List.append uu____8105 [t2]
              | uu____8108 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1338_8113 = top  in
              let uu____8114 =
                let uu____8115 =
                  let uu____8126 =
                    FStar_List.map
                      (fun uu____8137  -> FStar_Util.Inr uu____8137) terms
                     in
                  (uu____8126, rhs)  in
                FStar_Parser_AST.Sum uu____8115  in
              {
                FStar_Parser_AST.tm = uu____8114;
                FStar_Parser_AST.range =
                  (uu___1338_8113.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1338_8113.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8145 =
              let uu____8146 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8146  in
            (uu____8145, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8152 =
              let uu____8158 =
                let uu____8160 =
                  let uu____8162 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8162 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8160  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8158)  in
            FStar_Errors.raise_error uu____8152 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8177 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8177 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8184 =
                   let uu____8190 =
                     let uu____8192 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8192
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8190)
                    in
                 FStar_Errors.raise_error uu____8184
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8207 =
                     let uu____8232 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8294 = desugar_term_aq env t  in
                               match uu____8294 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8232 FStar_List.unzip  in
                   (match uu____8207 with
                    | (args1,aqs) ->
                        let uu____8427 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8427, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8444)::[]) when
            let uu____8459 = FStar_Ident.string_of_lid n  in
            uu____8459 = "SMTPat" ->
            let uu____8463 =
              let uu___1367_8464 = top  in
              let uu____8465 =
                let uu____8466 =
                  let uu____8473 =
                    let uu___1369_8474 = top  in
                    let uu____8475 =
                      let uu____8476 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8476  in
                    {
                      FStar_Parser_AST.tm = uu____8475;
                      FStar_Parser_AST.range =
                        (uu___1369_8474.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1369_8474.FStar_Parser_AST.level)
                    }  in
                  (uu____8473, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8466  in
              {
                FStar_Parser_AST.tm = uu____8465;
                FStar_Parser_AST.range =
                  (uu___1367_8464.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1367_8464.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8463
        | FStar_Parser_AST.Construct (n,(a,uu____8479)::[]) when
            let uu____8494 = FStar_Ident.string_of_lid n  in
            uu____8494 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8501 =
                let uu___1379_8502 = top  in
                let uu____8503 =
                  let uu____8504 =
                    let uu____8511 =
                      let uu___1381_8512 = top  in
                      let uu____8513 =
                        let uu____8514 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8514  in
                      {
                        FStar_Parser_AST.tm = uu____8513;
                        FStar_Parser_AST.range =
                          (uu___1381_8512.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1381_8512.FStar_Parser_AST.level)
                      }  in
                    (uu____8511, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8504  in
                {
                  FStar_Parser_AST.tm = uu____8503;
                  FStar_Parser_AST.range =
                    (uu___1379_8502.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1379_8502.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8501))
        | FStar_Parser_AST.Construct (n,(a,uu____8517)::[]) when
            let uu____8532 = FStar_Ident.string_of_lid n  in
            uu____8532 = "SMTPatOr" ->
            let uu____8536 =
              let uu___1390_8537 = top  in
              let uu____8538 =
                let uu____8539 =
                  let uu____8546 =
                    let uu___1392_8547 = top  in
                    let uu____8548 =
                      let uu____8549 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8549  in
                    {
                      FStar_Parser_AST.tm = uu____8548;
                      FStar_Parser_AST.range =
                        (uu___1392_8547.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1392_8547.FStar_Parser_AST.level)
                    }  in
                  (uu____8546, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8539  in
              {
                FStar_Parser_AST.tm = uu____8538;
                FStar_Parser_AST.range =
                  (uu___1390_8537.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1390_8537.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8536
        | FStar_Parser_AST.Name lid when
            let uu____8551 = FStar_Ident.string_of_lid lid  in
            uu____8551 = "Type0" ->
            let uu____8555 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8555, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8557 = FStar_Ident.string_of_lid lid  in
            uu____8557 = "Type" ->
            let uu____8561 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8561, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8578 = FStar_Ident.string_of_lid lid  in
            uu____8578 = "Type" ->
            let uu____8582 =
              let uu____8583 =
                let uu____8584 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8584  in
              mk uu____8583  in
            (uu____8582, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8586 = FStar_Ident.string_of_lid lid  in
            uu____8586 = "Effect" ->
            let uu____8590 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8590, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8592 = FStar_Ident.string_of_lid lid  in
            uu____8592 = "True" ->
            let uu____8596 =
              let uu____8597 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8597
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8596, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8599 = FStar_Ident.string_of_lid lid  in
            uu____8599 = "False" ->
            let uu____8603 =
              let uu____8604 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8604
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8603, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8609 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8609) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8613 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8613 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8622 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8622, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8624 =
                   let uu____8626 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8626 txt
                    in
                 failwith uu____8624)
        | FStar_Parser_AST.Var l ->
            let uu____8634 = desugar_name mk setpos env true l  in
            (uu____8634, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8642 = desugar_name mk setpos env true l  in
            (uu____8642, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8659 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8659 with
              | FStar_Pervasives_Native.Some uu____8669 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8677 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8677 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8695 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8716 =
                   let uu____8717 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8717  in
                 (uu____8716, noaqs)
             | uu____8723 ->
                 let uu____8731 =
                   let uu____8737 =
                     let uu____8739 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8739
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8737)  in
                 FStar_Errors.raise_error uu____8731
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8748 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8748 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8755 =
                   let uu____8761 =
                     let uu____8763 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8763
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8761)
                    in
                 FStar_Errors.raise_error uu____8755
                   top.FStar_Parser_AST.range
             | uu____8771 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8775 = desugar_name mk setpos env true lid'  in
                 (uu____8775, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8796 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8796 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8815 ->
                      let uu____8822 =
                        FStar_Util.take
                          (fun uu____8846  ->
                             match uu____8846 with
                             | (uu____8852,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8822 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8897 =
                             let uu____8922 =
                               FStar_List.map
                                 (fun uu____8965  ->
                                    match uu____8965 with
                                    | (t,imp) ->
                                        let uu____8982 =
                                          desugar_term_aq env t  in
                                        (match uu____8982 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8922 FStar_List.unzip
                              in
                           (match uu____8897 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9125 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9125, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9144 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9144 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9152 =
                         let uu____9154 =
                           let uu____9156 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9156 " not found"  in
                         Prims.op_Hat "Constructor " uu____9154  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9152)
                   | FStar_Pervasives_Native.Some uu____9161 ->
                       let uu____9162 =
                         let uu____9164 =
                           let uu____9166 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9166
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9164  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9162)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9195  ->
                 match uu___8_9195 with
                 | FStar_Util.Inr uu____9201 -> true
                 | uu____9203 -> false) binders
            ->
            let terms =
              let uu____9212 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9229  ->
                        match uu___9_9229 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9235 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9212 [t]  in
            let uu____9237 =
              let uu____9262 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9319 = desugar_typ_aq env t1  in
                        match uu____9319 with
                        | (t',aq) ->
                            let uu____9330 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9330, aq)))
                 in
              FStar_All.pipe_right uu____9262 FStar_List.unzip  in
            (match uu____9237 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9440 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9440
                    in
                 let uu____9449 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9449, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9476 =
              let uu____9493 =
                let uu____9500 =
                  let uu____9507 =
                    FStar_All.pipe_left
                      (fun uu____9516  -> FStar_Util.Inl uu____9516)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9507]  in
                FStar_List.append binders uu____9500  in
              FStar_List.fold_left
                (fun uu____9561  ->
                   fun b  ->
                     match uu____9561 with
                     | (env1,tparams,typs) ->
                         let uu____9622 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9637 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9637)
                            in
                         (match uu____9622 with
                          | (xopt,t1) ->
                              let uu____9662 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9671 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9671)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9662 with
                               | (env2,x) ->
                                   let uu____9691 =
                                     let uu____9694 =
                                       let uu____9697 =
                                         let uu____9698 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9698
                                          in
                                       [uu____9697]  in
                                     FStar_List.append typs uu____9694  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1521_9724 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1521_9724.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1521_9724.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9691)))) (env, [], []) uu____9493
               in
            (match uu____9476 with
             | (env1,uu____9752,targs) ->
                 let tup =
                   let uu____9775 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9775
                    in
                 let uu____9776 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9776, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9795 = uncurry binders t  in
            (match uu____9795 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9839 =
                   match uu___10_9839 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9856 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9856
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9880 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9880 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9913 = aux env [] bs  in (uu____9913, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9922 = desugar_binder env b  in
            (match uu____9922 with
             | (FStar_Pervasives_Native.None ,uu____9933) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9948 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9948 with
                  | ((x,uu____9964),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9977 =
                        let uu____9978 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9978  in
                      (uu____9977, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10056 = FStar_Util.set_is_empty i  in
                    if uu____10056
                    then
                      let uu____10061 = FStar_Util.set_union acc set  in
                      aux uu____10061 sets2
                    else
                      (let uu____10066 =
                         let uu____10067 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10067  in
                       FStar_Pervasives_Native.Some uu____10066)
                 in
              let uu____10070 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10070 sets  in
            ((let uu____10074 = check_disjoint bvss  in
              match uu____10074 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10078 =
                    let uu____10084 =
                      let uu____10086 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10086
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10084)
                     in
                  let uu____10090 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10078 uu____10090);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10098 =
                FStar_List.fold_left
                  (fun uu____10118  ->
                     fun pat  ->
                       match uu____10118 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10144,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10154 =
                                  let uu____10157 = free_type_vars env1 t  in
                                  FStar_List.append uu____10157 ftvs  in
                                (env1, uu____10154)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10162,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10173 =
                                  let uu____10176 = free_type_vars env1 t  in
                                  let uu____10179 =
                                    let uu____10182 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10182 ftvs  in
                                  FStar_List.append uu____10176 uu____10179
                                   in
                                (env1, uu____10173)
                            | uu____10187 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10098 with
              | (uu____10196,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10208 =
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
                    FStar_List.append uu____10208 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10288 = desugar_term_aq env1 body  in
                        (match uu____10288 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10323 =
                                       let uu____10324 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10324
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10323
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
                             let uu____10393 =
                               let uu____10394 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10394  in
                             (uu____10393, aq))
                    | p::rest ->
                        let uu____10407 = desugar_binding_pat env1 p  in
                        (match uu____10407 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10439)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10454 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10463 =
                               match b with
                               | LetBinder uu____10504 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10573) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10627 =
                                           let uu____10636 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10636, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10627
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10698,uu____10699) ->
                                              let tup2 =
                                                let uu____10701 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10701
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10706 =
                                                  let uu____10713 =
                                                    let uu____10714 =
                                                      let uu____10731 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10734 =
                                                        let uu____10745 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10754 =
                                                          let uu____10765 =
                                                            let uu____10774 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10774
                                                             in
                                                          [uu____10765]  in
                                                        uu____10745 ::
                                                          uu____10754
                                                         in
                                                      (uu____10731,
                                                        uu____10734)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10714
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10713
                                                   in
                                                uu____10706
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10822 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10822
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10873,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10875,pats1)) ->
                                              let tupn =
                                                let uu____10920 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10920
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10933 =
                                                  let uu____10934 =
                                                    let uu____10951 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10954 =
                                                      let uu____10965 =
                                                        let uu____10976 =
                                                          let uu____10985 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10985
                                                           in
                                                        [uu____10976]  in
                                                      FStar_List.append args
                                                        uu____10965
                                                       in
                                                    (uu____10951,
                                                      uu____10954)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10934
                                                   in
                                                mk uu____10933  in
                                              let p2 =
                                                let uu____11033 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11033
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11080 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10463 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11172,uu____11173,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11195 =
                let uu____11196 = unparen e  in
                uu____11196.FStar_Parser_AST.tm  in
              match uu____11195 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11206 ->
                  let uu____11207 = desugar_term_aq env e  in
                  (match uu____11207 with
                   | (head,aq) ->
                       let uu____11220 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11220, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11227 ->
            let rec aux args aqs e =
              let uu____11304 =
                let uu____11305 = unparen e  in
                uu____11305.FStar_Parser_AST.tm  in
              match uu____11304 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11323 = desugar_term_aq env t  in
                  (match uu____11323 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11371 ->
                  let uu____11372 = desugar_term_aq env e  in
                  (match uu____11372 with
                   | (head,aq) ->
                       let uu____11393 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11393, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11446 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11446
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11453 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11453  in
            let bind =
              let uu____11458 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11458 FStar_Parser_AST.Expr
               in
            let uu____11459 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11459
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
            let uu____11511 = desugar_term_aq env t  in
            (match uu____11511 with
             | (tm,s) ->
                 let uu____11522 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11522, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11528 =
              let uu____11541 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11541 then desugar_typ_aq else desugar_term_aq  in
            uu____11528 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11608 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11751  ->
                        match uu____11751 with
                        | (attr_opt,(p,def)) ->
                            let uu____11809 = is_app_pattern p  in
                            if uu____11809
                            then
                              let uu____11842 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11842, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11925 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11925, def1)
                               | uu____11970 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____12008);
                                           FStar_Parser_AST.prange =
                                             uu____12009;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12058 =
                                            let uu____12079 =
                                              let uu____12084 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12084  in
                                            (uu____12079, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12058, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12176) ->
                                        if top_level
                                        then
                                          let uu____12212 =
                                            let uu____12233 =
                                              let uu____12238 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12238  in
                                            (uu____12233, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12212, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12329 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12362 =
                FStar_List.fold_left
                  (fun uu____12451  ->
                     fun uu____12452  ->
                       match (uu____12451, uu____12452) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12582,uu____12583),uu____12584))
                           ->
                           let uu____12718 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12758 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12758 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12793 =
                                        let uu____12796 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12796 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12793, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12812 =
                                   let uu____12820 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12820
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12812 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12718 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12362 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13066 =
                    match uu____13066 with
                    | (attrs_opt,(uu____13106,args,result_t),def) ->
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
                                let uu____13198 = is_comp_type env1 t  in
                                if uu____13198
                                then
                                  ((let uu____13202 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13212 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13212))
                                       in
                                    match uu____13202 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13219 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13222 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13222))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13219
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
                          | uu____13233 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13236 = desugar_term_aq env1 def2  in
                        (match uu____13236 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13258 =
                                     let uu____13259 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13259
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13258
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
                  let uu____13300 =
                    let uu____13317 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13317 FStar_List.unzip  in
                  (match uu____13300 with
                   | (lbs1,aqss) ->
                       let uu____13459 = desugar_term_aq env' body  in
                       (match uu____13459 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13565  ->
                                    fun used_marker  ->
                                      match uu____13565 with
                                      | (_attr_opt,(f,uu____13639,uu____13640),uu____13641)
                                          ->
                                          let uu____13698 =
                                            let uu____13700 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13700  in
                                          if uu____13698
                                          then
                                            let uu____13724 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13742 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13744 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13742, "Local",
                                                    uu____13744)
                                              | FStar_Util.Inr l ->
                                                  let uu____13749 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13751 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13749, "Global",
                                                    uu____13751)
                                               in
                                            (match uu____13724 with
                                             | (nm,gl,rng) ->
                                                 let uu____13762 =
                                                   let uu____13768 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13768)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13762)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13776 =
                                let uu____13779 =
                                  let uu____13780 =
                                    let uu____13794 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13794)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13780  in
                                FStar_All.pipe_left mk uu____13779  in
                              (uu____13776,
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
              let uu____13896 = desugar_term_aq env t1  in
              match uu____13896 with
              | (t11,aq0) ->
                  let uu____13917 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13917 with
                   | (env1,binder,pat1) ->
                       let uu____13947 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13989 = desugar_term_aq env1 t2  in
                             (match uu____13989 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____14011 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14011
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____14012 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____14012, aq))
                         | LocalBinder (x,uu____14053) ->
                             let uu____14054 = desugar_term_aq env1 t2  in
                             (match uu____14054 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14076;
                                         FStar_Syntax_Syntax.p = uu____14077;_},uu____14078)::[]
                                        -> body1
                                    | uu____14091 ->
                                        let uu____14094 =
                                          let uu____14101 =
                                            let uu____14102 =
                                              let uu____14125 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14128 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14125, uu____14128)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14102
                                             in
                                          FStar_Syntax_Syntax.mk uu____14101
                                           in
                                        uu____14094
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14165 =
                                    let uu____14168 =
                                      let uu____14169 =
                                        let uu____14183 =
                                          let uu____14186 =
                                            let uu____14187 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14187]  in
                                          FStar_Syntax_Subst.close
                                            uu____14186 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14183)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14169
                                       in
                                    FStar_All.pipe_left mk uu____14168  in
                                  (uu____14165, aq))
                          in
                       (match uu____13947 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14295 = FStar_List.hd lbs  in
            (match uu____14295 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14339 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14339
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14355 =
                let uu____14356 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14356  in
              mk uu____14355  in
            let uu____14357 = desugar_term_aq env t1  in
            (match uu____14357 with
             | (t1',aq1) ->
                 let uu____14368 = desugar_term_aq env t2  in
                 (match uu____14368 with
                  | (t2',aq2) ->
                      let uu____14379 = desugar_term_aq env t3  in
                      (match uu____14379 with
                       | (t3',aq3) ->
                           let uu____14390 =
                             let uu____14391 =
                               let uu____14392 =
                                 let uu____14415 =
                                   let uu____14432 =
                                     let uu____14447 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14447,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14461 =
                                     let uu____14478 =
                                       let uu____14493 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14493,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14478]  in
                                   uu____14432 :: uu____14461  in
                                 (t1', uu____14415)  in
                               FStar_Syntax_Syntax.Tm_match uu____14392  in
                             mk uu____14391  in
                           (uu____14390, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14689 =
              match uu____14689 with
              | (pat,wopt,b) ->
                  let uu____14711 = desugar_match_pat env pat  in
                  (match uu____14711 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14742 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14742
                          in
                       let uu____14747 = desugar_term_aq env1 b  in
                       (match uu____14747 with
                        | (b1,aq) ->
                            let uu____14760 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14760, aq)))
               in
            let uu____14765 = desugar_term_aq env e  in
            (match uu____14765 with
             | (e1,aq) ->
                 let uu____14776 =
                   let uu____14807 =
                     let uu____14840 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14840 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14807
                     (fun uu____15058  ->
                        match uu____15058 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14776 with
                  | (brs,aqs) ->
                      let uu____15277 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15277, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15311 =
              let uu____15332 = is_comp_type env t  in
              if uu____15332
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15387 = desugar_term_aq env t  in
                 match uu____15387 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15311 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15479 = desugar_term_aq env e  in
                 (match uu____15479 with
                  | (e1,aq) ->
                      let uu____15490 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15490, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15529,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15572 = FStar_List.hd fields  in
              match uu____15572 with
              | (f,uu____15584) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15632  ->
                        match uu____15632 with
                        | (g,uu____15639) ->
                            let uu____15640 = FStar_Ident.text_of_id f  in
                            let uu____15642 =
                              let uu____15644 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15644  in
                            uu____15640 = uu____15642))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15651,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15665 =
                         let uu____15671 =
                           let uu____15673 = FStar_Ident.text_of_id f  in
                           let uu____15675 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15673 uu____15675
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15671)
                          in
                       FStar_Errors.raise_error uu____15665
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
                  let uu____15686 =
                    let uu____15697 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15728  ->
                              match uu____15728 with
                              | (f,uu____15738) ->
                                  let uu____15739 =
                                    let uu____15740 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15740
                                     in
                                  (uu____15739, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15697)  in
                  FStar_Parser_AST.Construct uu____15686
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15758 =
                      let uu____15759 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15759  in
                    let uu____15760 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15758 uu____15760
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15762 =
                      let uu____15775 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15805  ->
                                match uu____15805 with
                                | (f,uu____15815) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15775)  in
                    FStar_Parser_AST.Record uu____15762  in
                  let uu____15824 =
                    let uu____15845 =
                      let uu____15860 =
                        let uu____15873 =
                          let uu____15878 =
                            let uu____15879 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15879
                             in
                          (uu____15878, e)  in
                        (FStar_Pervasives_Native.None, uu____15873)  in
                      [uu____15860]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15845,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15824
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15931 = desugar_term_aq env recterm1  in
            (match uu____15931 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15947;
                         FStar_Syntax_Syntax.vars = uu____15948;_},args)
                      ->
                      let uu____15974 =
                        let uu____15975 =
                          let uu____15976 =
                            let uu____15993 =
                              let uu____15996 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15997 =
                                let uu____16000 =
                                  let uu____16001 =
                                    let uu____16008 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____16008)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____16001
                                   in
                                FStar_Pervasives_Native.Some uu____16000  in
                              FStar_Syntax_Syntax.fvar uu____15996
                                FStar_Syntax_Syntax.delta_constant
                                uu____15997
                               in
                            (uu____15993, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15976  in
                        FStar_All.pipe_left mk uu____15975  in
                      (uu____15974, s)
                  | uu____16037 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16040 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16040 with
             | (constrname,is_rec) ->
                 let uu____16059 = desugar_term_aq env e  in
                 (match uu____16059 with
                  | (e1,s) ->
                      let projname =
                        let uu____16071 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16071
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16078 =
                            let uu____16079 =
                              let uu____16084 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16084)  in
                            FStar_Syntax_Syntax.Record_projector uu____16079
                             in
                          FStar_Pervasives_Native.Some uu____16078
                        else FStar_Pervasives_Native.None  in
                      let uu____16087 =
                        let uu____16088 =
                          let uu____16089 =
                            let uu____16106 =
                              let uu____16109 =
                                let uu____16110 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16110
                                 in
                              FStar_Syntax_Syntax.fvar uu____16109
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16112 =
                              let uu____16123 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16123]  in
                            (uu____16106, uu____16112)  in
                          FStar_Syntax_Syntax.Tm_app uu____16089  in
                        FStar_All.pipe_left mk uu____16088  in
                      (uu____16087, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16163 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16163
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16174 =
              let uu____16175 = FStar_Syntax_Subst.compress tm  in
              uu____16175.FStar_Syntax_Syntax.n  in
            (match uu____16174 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16183 =
                   let uu___2089_16184 =
                     let uu____16185 =
                       let uu____16187 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16187  in
                     FStar_Syntax_Util.exp_string uu____16185  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2089_16184.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2089_16184.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16183, noaqs)
             | uu____16188 ->
                 let uu____16189 =
                   let uu____16195 =
                     let uu____16197 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16197
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16195)  in
                 FStar_Errors.raise_error uu____16189
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16206 = desugar_term_aq env e  in
            (match uu____16206 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16218 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16218, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16223 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16224 =
              let uu____16225 =
                let uu____16232 = desugar_term env e  in (bv, uu____16232)
                 in
              [uu____16225]  in
            (uu____16223, uu____16224)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16257 =
              let uu____16258 =
                let uu____16259 =
                  let uu____16266 = desugar_term env e  in (uu____16266, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16259  in
              FStar_All.pipe_left mk uu____16258  in
            (uu____16257, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16295 -> false  in
              let uu____16297 =
                let uu____16298 = unparen rel1  in
                uu____16298.FStar_Parser_AST.tm  in
              match uu____16297 with
              | FStar_Parser_AST.Op (id,uu____16301) ->
                  let uu____16306 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id
                     in
                  (match uu____16306 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16314 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16314 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16325 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16325 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16331 -> false  in
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
              let uu____16352 =
                let uu____16353 =
                  let uu____16360 =
                    let uu____16361 =
                      let uu____16362 =
                        let uu____16371 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16384 =
                          let uu____16385 =
                            let uu____16386 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16386  in
                          FStar_Parser_AST.mk_term uu____16385
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16371, uu____16384,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16362  in
                    FStar_Parser_AST.mk_term uu____16361
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16360)  in
                FStar_Parser_AST.Abs uu____16353  in
              FStar_Parser_AST.mk_term uu____16352
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
              let uu____16407 = FStar_List.last steps  in
              match uu____16407 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16410,uu____16411,last_expr)) -> last_expr
              | uu____16413 -> failwith "impossible: no last_expr on calc"
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
            let uu____16441 =
              FStar_List.fold_left
                (fun uu____16459  ->
                   fun uu____16460  ->
                     match (uu____16459, uu____16460) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16483 = is_impl rel2  in
                           if uu____16483
                           then
                             let uu____16486 =
                               let uu____16493 =
                                 let uu____16498 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16498, FStar_Parser_AST.Nothing)  in
                               [uu____16493]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16486 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16510 =
                             let uu____16517 =
                               let uu____16524 =
                                 let uu____16531 =
                                   let uu____16538 =
                                     let uu____16543 = eta_and_annot rel2  in
                                     (uu____16543, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16544 =
                                     let uu____16551 =
                                       let uu____16558 =
                                         let uu____16563 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16563,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16564 =
                                         let uu____16571 =
                                           let uu____16576 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16576,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16571]  in
                                       uu____16558 :: uu____16564  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16551
                                      in
                                   uu____16538 :: uu____16544  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16531
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16524
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16517
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16510
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16441 with
             | (e1,uu____16614) ->
                 let e2 =
                   let uu____16616 =
                     let uu____16623 =
                       let uu____16630 =
                         let uu____16637 =
                           let uu____16642 = FStar_Parser_AST.thunk e1  in
                           (uu____16642, FStar_Parser_AST.Nothing)  in
                         [uu____16637]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16630  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16623  in
                   FStar_Parser_AST.mkApp finish uu____16616
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16659 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16660 = desugar_formula env top  in
            (uu____16660, noaqs)
        | uu____16661 ->
            let uu____16662 =
              let uu____16668 =
                let uu____16670 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16670  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16668)  in
            FStar_Errors.raise_error uu____16662 top.FStar_Parser_AST.range

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
           (fun uu____16714  ->
              match uu____16714 with
              | (a,imp) ->
                  let uu____16727 = desugar_term env a  in
                  arg_withimp_e imp uu____16727))

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
          let is_requires uu____16764 =
            match uu____16764 with
            | (t1,uu____16771) ->
                let uu____16772 =
                  let uu____16773 = unparen t1  in
                  uu____16773.FStar_Parser_AST.tm  in
                (match uu____16772 with
                 | FStar_Parser_AST.Requires uu____16775 -> true
                 | uu____16784 -> false)
             in
          let is_ensures uu____16796 =
            match uu____16796 with
            | (t1,uu____16803) ->
                let uu____16804 =
                  let uu____16805 = unparen t1  in
                  uu____16805.FStar_Parser_AST.tm  in
                (match uu____16804 with
                 | FStar_Parser_AST.Ensures uu____16807 -> true
                 | uu____16816 -> false)
             in
          let is_app head uu____16834 =
            match uu____16834 with
            | (t1,uu____16842) ->
                let uu____16843 =
                  let uu____16844 = unparen t1  in
                  uu____16844.FStar_Parser_AST.tm  in
                (match uu____16843 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16847;
                        FStar_Parser_AST.level = uu____16848;_},uu____16849,uu____16850)
                     ->
                     let uu____16851 =
                       let uu____16853 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16853  in
                     uu____16851 = head
                 | uu____16855 -> false)
             in
          let is_smt_pat uu____16867 =
            match uu____16867 with
            | (t1,uu____16874) ->
                let uu____16875 =
                  let uu____16876 = unparen t1  in
                  uu____16876.FStar_Parser_AST.tm  in
                (match uu____16875 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16880);
                              FStar_Parser_AST.range = uu____16881;
                              FStar_Parser_AST.level = uu____16882;_},uu____16883)::uu____16884::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16924 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16924 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16936;
                              FStar_Parser_AST.level = uu____16937;_},uu____16938)::uu____16939::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16967 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16967 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16975 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____17010 = head_and_args t1  in
            match uu____17010 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17068 =
                       let uu____17070 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17070  in
                     uu____17068 = "Lemma" ->
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
                     let thunk_ens uu____17106 =
                       match uu____17106 with
                       | (e,i) ->
                           let uu____17117 = FStar_Parser_AST.thunk e  in
                           (uu____17117, i)
                        in
                     let fail_lemma uu____17129 =
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
                           let uu____17235 =
                             let uu____17242 =
                               let uu____17249 = thunk_ens ens  in
                               [uu____17249; nil_pat]  in
                             req_true :: uu____17242  in
                           unit_tm :: uu____17235
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17296 =
                             let uu____17303 =
                               let uu____17310 = thunk_ens ens  in
                               [uu____17310; nil_pat]  in
                             req :: uu____17303  in
                           unit_tm :: uu____17296
                       | ens::smtpat::[] when
                           (((let uu____17359 = is_requires ens  in
                              Prims.op_Negation uu____17359) &&
                               (let uu____17362 = is_smt_pat ens  in
                                Prims.op_Negation uu____17362))
                              &&
                              (let uu____17365 = is_decreases ens  in
                               Prims.op_Negation uu____17365))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17367 =
                             let uu____17374 =
                               let uu____17381 = thunk_ens ens  in
                               [uu____17381; smtpat]  in
                             req_true :: uu____17374  in
                           unit_tm :: uu____17367
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17428 =
                             let uu____17435 =
                               let uu____17442 = thunk_ens ens  in
                               [uu____17442; nil_pat; dec]  in
                             req_true :: uu____17435  in
                           unit_tm :: uu____17428
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17502 =
                             let uu____17509 =
                               let uu____17516 = thunk_ens ens  in
                               [uu____17516; smtpat; dec]  in
                             req_true :: uu____17509  in
                           unit_tm :: uu____17502
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17576 =
                             let uu____17583 =
                               let uu____17590 = thunk_ens ens  in
                               [uu____17590; nil_pat; dec]  in
                             req :: uu____17583  in
                           unit_tm :: uu____17576
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17650 =
                             let uu____17657 =
                               let uu____17664 = thunk_ens ens  in
                               [uu____17664; smtpat]  in
                             req :: uu____17657  in
                           unit_tm :: uu____17650
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17729 =
                             let uu____17736 =
                               let uu____17743 = thunk_ens ens  in
                               [uu____17743; dec; smtpat]  in
                             req :: uu____17736  in
                           unit_tm :: uu____17729
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17805 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17805, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17833 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17833
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17835 =
                          let uu____17837 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17837  in
                        uu____17835 = "Tot")
                     ->
                     let uu____17840 =
                       let uu____17847 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17847, [])  in
                     (uu____17840, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17865 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17865
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17867 =
                          let uu____17869 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17869  in
                        uu____17867 = "GTot")
                     ->
                     let uu____17872 =
                       let uu____17879 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17879, [])  in
                     (uu____17872, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17897 =
                         let uu____17899 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17899  in
                       uu____17897 = "Type") ||
                        (let uu____17903 =
                           let uu____17905 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17905  in
                         uu____17903 = "Type0"))
                       ||
                       (let uu____17909 =
                          let uu____17911 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17911  in
                        uu____17909 = "Effect")
                     ->
                     let uu____17914 =
                       let uu____17921 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17921, [])  in
                     (uu____17914, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17944 when allow_type_promotion ->
                     let default_effect =
                       let uu____17946 = FStar_Options.ml_ish ()  in
                       if uu____17946
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17952 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17952
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17959 =
                       let uu____17966 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17966, [])  in
                     (uu____17959, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17989 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____18008 = pre_process_comp_typ t  in
          match uu____18008 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18060 =
                    let uu____18066 =
                      let uu____18068 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18068
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18066)
                     in
                  fail uu____18060)
               else ();
               (let is_universe uu____18084 =
                  match uu____18084 with
                  | (uu____18090,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18092 = FStar_Util.take is_universe args  in
                match uu____18092 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18151  ->
                           match uu____18151 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18158 =
                      let uu____18173 = FStar_List.hd args1  in
                      let uu____18182 = FStar_List.tl args1  in
                      (uu____18173, uu____18182)  in
                    (match uu____18158 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18237 =
                           let is_decrease uu____18276 =
                             match uu____18276 with
                             | (t1,uu____18287) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18298;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18299;_},uu____18300::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18339 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18237 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18456  ->
                                        match uu____18456 with
                                        | (t1,uu____18466) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18475,(arg,uu____18477)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18516 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18537 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18549 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18549
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18556 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18556
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18566 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18566
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18573 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18573
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18580 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18580
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18587 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18587
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18608 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18608
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
                                                    let uu____18699 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18699
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
                                              | uu____18720 -> pat  in
                                            let uu____18721 =
                                              let uu____18732 =
                                                let uu____18743 =
                                                  let uu____18752 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18752, aq)  in
                                                [uu____18743]  in
                                              ens :: uu____18732  in
                                            req :: uu____18721
                                        | uu____18793 -> rest2
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
        let uu___2414_18828 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2414_18828.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2414_18828.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2421_18882 = b  in
             {
               FStar_Parser_AST.b = (uu___2421_18882.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2421_18882.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2421_18882.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18911 body1 =
          match uu____18911 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18957::uu____18958) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18976 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2440_19004 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____19005 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2440_19004.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____19005;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2440_19004.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19068 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19068))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19099 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19099 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2453_19109 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2453_19109.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2453_19109.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19115 =
                     let uu____19118 =
                       let uu____19119 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19119]  in
                     no_annot_abs uu____19118 body2  in
                   FStar_All.pipe_left setpos uu____19115  in
                 let uu____19140 =
                   let uu____19141 =
                     let uu____19158 =
                       let uu____19161 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19161
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19163 =
                       let uu____19174 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19174]  in
                     (uu____19158, uu____19163)  in
                   FStar_Syntax_Syntax.Tm_app uu____19141  in
                 FStar_All.pipe_left mk uu____19140)
        | uu____19213 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19278 = q (rest, pats, body)  in
              let uu____19281 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19278 uu____19281
                FStar_Parser_AST.Formula
               in
            let uu____19282 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19282 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19293 -> failwith "impossible"  in
      let uu____19297 =
        let uu____19298 = unparen f  in uu____19298.FStar_Parser_AST.tm  in
      match uu____19297 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19311,uu____19312) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19336,uu____19337) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19393 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19393
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19437 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19437
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19501 -> desugar_term env f

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
          let uu____19512 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19512)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19517 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19517)
      | FStar_Parser_AST.TVariable x ->
          let uu____19521 =
            let uu____19522 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19522
             in
          ((FStar_Pervasives_Native.Some x), uu____19521)
      | FStar_Parser_AST.NoName t ->
          let uu____19526 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19526)
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
      fun uu___11_19534  ->
        match uu___11_19534 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19556 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19556, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19573 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19573 with
             | (env1,a1) ->
                 let uu____19590 =
                   let uu____19597 = trans_aqual env1 imp  in
                   ((let uu___2553_19603 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2553_19603.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2553_19603.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19597)
                    in
                 (uu____19590, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19611  ->
      match uu___12_19611 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19615 =
            let uu____19616 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19616  in
          FStar_Pervasives_Native.Some uu____19615
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19644 =
        FStar_List.fold_left
          (fun uu____19677  ->
             fun b  ->
               match uu____19677 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2571_19721 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2571_19721.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2571_19721.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2571_19721.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19736 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19736 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2581_19754 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2581_19754.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2581_19754.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19755 =
                               let uu____19762 =
                                 let uu____19767 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19767)  in
                               uu____19762 :: out  in
                             (env2, uu____19755))
                    | uu____19778 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19644 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19866 =
          let uu____19867 = unparen t  in uu____19867.FStar_Parser_AST.tm  in
        match uu____19866 with
        | FStar_Parser_AST.Var lid when
            let uu____19869 = FStar_Ident.string_of_lid lid  in
            uu____19869 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19873 ->
            let uu____19874 =
              let uu____19880 =
                let uu____19882 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19882  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19880)  in
            FStar_Errors.raise_error uu____19874 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19899) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19901) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19904 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19922 = binder_ident b  in
         FStar_Common.list_of_option uu____19922) bs
  
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
               (fun uu___13_19959  ->
                  match uu___13_19959 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19964 -> false))
           in
        let quals2 q =
          let uu____19978 =
            (let uu____19982 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19982) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19978
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19999 = FStar_Ident.range_of_lid disc_name  in
                let uu____20000 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19999;
                  FStar_Syntax_Syntax.sigquals = uu____20000;
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
            let uu____20040 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20076  ->
                        match uu____20076 with
                        | (x,uu____20087) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20097 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20097)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20099 =
                                   let uu____20101 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20101  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20099)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20119 =
                                  FStar_List.filter
                                    (fun uu___14_20123  ->
                                       match uu___14_20123 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20126 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20119
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20141  ->
                                        match uu___15_20141 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20146 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20149 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20149;
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
                                 let uu____20156 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20156
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20167 =
                                   let uu____20172 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20172  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20167;
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
                                 let uu____20176 =
                                   let uu____20177 =
                                     let uu____20184 =
                                       let uu____20187 =
                                         let uu____20188 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20188
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20187]  in
                                     ((false, [lb]), uu____20184)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20177
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20176;
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
            FStar_All.pipe_right uu____20040 FStar_List.flatten
  
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
            (lid,uu____20237,t,uu____20239,n,uu____20241) when
            let uu____20248 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20248 ->
            let uu____20250 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20250 with
             | (formals,uu____20260) ->
                 (match formals with
                  | [] -> []
                  | uu____20273 ->
                      let filter_records uu___16_20281 =
                        match uu___16_20281 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20284,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20296 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20298 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20298 with
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
                      let uu____20310 = FStar_Util.first_N n formals  in
                      (match uu____20310 with
                       | (uu____20339,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20373 -> []
  
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
                        let uu____20467 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20467
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20491 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20491
                        then
                          let uu____20497 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20497
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20501 =
                          let uu____20506 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20506  in
                        let uu____20507 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20513 =
                              let uu____20516 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20516  in
                            FStar_Syntax_Util.arrow typars uu____20513
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20521 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20501;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20507;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20521;
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
          let tycon_id uu___17_20575 =
            match uu___17_20575 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20577,uu____20578) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20588,uu____20589,uu____20590) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20600,uu____20601,uu____20602) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20624,uu____20625,uu____20626) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20664) ->
                let uu____20665 =
                  let uu____20666 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20666  in
                let uu____20667 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20665 uu____20667
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20669 =
                  let uu____20670 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20670  in
                let uu____20671 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20669 uu____20671
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20673) ->
                let uu____20674 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20674 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20676 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20676 FStar_Parser_AST.Type_level
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
              | uu____20706 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20714 =
                     let uu____20715 =
                       let uu____20722 = binder_to_term b  in
                       (out, uu____20722, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20715  in
                   FStar_Parser_AST.mk_term uu____20714
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20734 =
            match uu___18_20734 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20766 =
                    let uu____20772 =
                      let uu____20774 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20774  in
                    let uu____20777 = FStar_Ident.range_of_id id  in
                    (uu____20772, uu____20777)  in
                  FStar_Ident.mk_ident uu____20766  in
                let mfields =
                  FStar_List.map
                    (fun uu____20790  ->
                       match uu____20790 with
                       | (x,t) ->
                           let uu____20797 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20797
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20799 =
                    let uu____20800 =
                      let uu____20801 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20801  in
                    let uu____20802 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20800 uu____20802
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20799 parms  in
                let constrTyp =
                  let uu____20804 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20804 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20810 = binder_idents parms  in id :: uu____20810
                   in
                (FStar_List.iter
                   (fun uu____20824  ->
                      match uu____20824 with
                      | (f,uu____20830) ->
                          let uu____20831 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20831
                          then
                            let uu____20836 =
                              let uu____20842 =
                                let uu____20844 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20844
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20842)
                               in
                            let uu____20848 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20836 uu____20848
                          else ()) fields;
                 (let uu____20851 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20851)))
            | uu____20905 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20945 =
            match uu___19_20945 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20969 = typars_of_binders _env binders  in
                (match uu____20969 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____21005 =
                         let uu____21006 =
                           let uu____21007 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____21007  in
                         let uu____21008 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____21006 uu____21008
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____21005 binders  in
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
                     let uu____21017 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____21017 with
                      | (_env1,uu____21034) ->
                          let uu____21041 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21041 with
                           | (_env2,uu____21058) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21065 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21108 =
              FStar_List.fold_left
                (fun uu____21142  ->
                   fun uu____21143  ->
                     match (uu____21142, uu____21143) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21212 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21212 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21108 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21303 =
                      let uu____21304 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21304  in
                    FStar_Pervasives_Native.Some uu____21303
                | uu____21305 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21313 = desugar_abstract_tc quals env [] tc  in
              (match uu____21313 with
               | (uu____21326,uu____21327,se,uu____21329) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21332,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21351 =
                                 let uu____21353 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21353  in
                               if uu____21351
                               then
                                 let uu____21356 =
                                   let uu____21362 =
                                     let uu____21364 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21364
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21362)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21356
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
                           | uu____21377 ->
                               let uu____21378 =
                                 let uu____21385 =
                                   let uu____21386 =
                                     let uu____21401 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21401)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21386
                                    in
                                 FStar_Syntax_Syntax.mk uu____21385  in
                               uu____21378 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2858_21414 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2858_21414.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2858_21414.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2858_21414.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2858_21414.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21415 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21430 = typars_of_binders env binders  in
              (match uu____21430 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21464 =
                           FStar_Util.for_some
                             (fun uu___20_21467  ->
                                match uu___20_21467 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21470 -> false) quals
                            in
                         if uu____21464
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21478 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21478
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21483 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21489  ->
                               match uu___21_21489 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21492 -> false))
                        in
                     if uu____21483
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21506 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21506
                     then
                       let uu____21512 =
                         let uu____21519 =
                           let uu____21520 = unparen t  in
                           uu____21520.FStar_Parser_AST.tm  in
                         match uu____21519 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21541 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21571)::args_rev ->
                                   let uu____21583 =
                                     let uu____21584 = unparen last_arg  in
                                     uu____21584.FStar_Parser_AST.tm  in
                                   (match uu____21583 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21612 -> ([], args))
                               | uu____21621 -> ([], args)  in
                             (match uu____21541 with
                              | (cattributes,args1) ->
                                  let uu____21660 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21660))
                         | uu____21671 -> (t, [])  in
                       match uu____21512 with
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
                                  (fun uu___22_21694  ->
                                     match uu___22_21694 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21697 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21705)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21725 = tycon_record_as_variant trec  in
              (match uu____21725 with
               | (t,fs) ->
                   let uu____21742 =
                     let uu____21745 =
                       let uu____21746 =
                         let uu____21755 =
                           let uu____21758 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21758  in
                         (uu____21755, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21746  in
                     uu____21745 :: quals  in
                   desugar_tycon env d uu____21742 [t])
          | uu____21763::uu____21764 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21922 = et  in
                match uu____21922 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22132 ->
                         let trec = tc  in
                         let uu____22152 = tycon_record_as_variant trec  in
                         (match uu____22152 with
                          | (t,fs) ->
                              let uu____22208 =
                                let uu____22211 =
                                  let uu____22212 =
                                    let uu____22221 =
                                      let uu____22224 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22224  in
                                    (uu____22221, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22212
                                   in
                                uu____22211 :: quals1  in
                              collect_tcs uu____22208 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22302 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22302 with
                          | (env2,uu____22359,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22496 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22496 with
                          | (env2,uu____22553,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22669 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22715 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22715 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23167  ->
                             match uu___24_23167 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23221,uu____23222);
                                    FStar_Syntax_Syntax.sigrng = uu____23223;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23224;
                                    FStar_Syntax_Syntax.sigmeta = uu____23225;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23226;
                                    FStar_Syntax_Syntax.sigopts = uu____23227;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23289 =
                                     typars_of_binders env1 binders  in
                                   match uu____23289 with
                                   | (env2,tpars1) ->
                                       let uu____23316 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23316 with
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
                                 let uu____23345 =
                                   let uu____23356 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23356)  in
                                 [uu____23345]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23392);
                                    FStar_Syntax_Syntax.sigrng = uu____23393;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23395;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23396;
                                    FStar_Syntax_Syntax.sigopts = uu____23397;_},constrs,tconstr,quals1)
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
                                 let uu____23488 = push_tparams env1 tpars
                                    in
                                 (match uu____23488 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23547  ->
                                             match uu____23547 with
                                             | (x,uu____23559) ->
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
                                        let uu____23570 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23570
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23593 =
                                        let uu____23612 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23689  ->
                                                  match uu____23689 with
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
                                                        let uu____23732 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23732
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
                                                                uu___23_23743
                                                                 ->
                                                                match uu___23_23743
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23755
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23763 =
                                                        let uu____23774 =
                                                          let uu____23775 =
                                                            let uu____23776 =
                                                              let uu____23792
                                                                =
                                                                let uu____23793
                                                                  =
                                                                  let uu____23796
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23796
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23793
                                                                 in
                                                              (name, univs,
                                                                uu____23792,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23776
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23775;
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
                                                        (tps, uu____23774)
                                                         in
                                                      (name, uu____23763)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23612
                                         in
                                      (match uu____23593 with
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
                             | uu____23928 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____24009  ->
                             match uu____24009 with | (uu____24020,se) -> se))
                      in
                   let uu____24034 =
                     let uu____24041 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24041 rng
                      in
                   (match uu____24034 with
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
                               (fun uu____24086  ->
                                  match uu____24086 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24134,tps,k,uu____24137,constrs)
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
                                      let uu____24158 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24173 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24190,uu____24191,uu____24192,uu____24193,uu____24194)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24201
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24173
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24205 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24212  ->
                                                          match uu___25_24212
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24214 ->
                                                              true
                                                          | uu____24224 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24205))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24158
                                  | uu____24226 -> []))
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
      let uu____24263 =
        FStar_List.fold_left
          (fun uu____24298  ->
             fun b  ->
               match uu____24298 with
               | (env1,binders1) ->
                   let uu____24342 = desugar_binder env1 b  in
                   (match uu____24342 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24365 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24365 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24418 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24263 with
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
          let uu____24522 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24529  ->
                    match uu___26_24529 with
                    | FStar_Syntax_Syntax.Reflectable uu____24531 -> true
                    | uu____24533 -> false))
             in
          if uu____24522
          then
            let monad_env =
              let uu____24537 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24537  in
            let reflect_lid =
              let uu____24539 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24539
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
        let warn1 uu____24590 =
          if warn
          then
            let uu____24592 =
              let uu____24598 =
                let uu____24600 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24600
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24598)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24592
          else ()  in
        let uu____24606 = FStar_Syntax_Util.head_and_args at  in
        match uu____24606 with
        | (hd,args) ->
            let uu____24659 =
              let uu____24660 = FStar_Syntax_Subst.compress hd  in
              uu____24660.FStar_Syntax_Syntax.n  in
            (match uu____24659 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24704)::[] ->
                      let uu____24729 =
                        let uu____24734 =
                          let uu____24743 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24743 a1  in
                        uu____24734 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24729 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24766 =
                             let uu____24772 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24772  in
                           (uu____24766, true)
                       | uu____24787 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24803 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24825 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24942 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24942 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24991 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24991 with | (res1,uu____25013) -> rebind res1 true)
  
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
        | uu____25340 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25398 = get_fail_attr1 warn at  in
             comb uu____25398 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25433 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25433 with
        | FStar_Pervasives_Native.None  ->
            let uu____25436 =
              let uu____25442 =
                let uu____25444 =
                  let uu____25446 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25446 " not found"  in
                Prims.op_Hat "Effect name " uu____25444  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25442)  in
            FStar_Errors.raise_error uu____25436 r
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
                    let uu____25602 = desugar_binders monad_env eff_binders
                       in
                    match uu____25602 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25641 =
                            let uu____25650 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25650  in
                          FStar_List.length uu____25641  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25668 =
                              let uu____25674 =
                                let uu____25676 =
                                  let uu____25678 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25678
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25676  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25674)
                               in
                            FStar_Errors.raise_error uu____25668
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
                                (uu____25746,uu____25747,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25749,uu____25750,uu____25751))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25766 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25769 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25781 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25781 mandatory_members)
                              eff_decls
                             in
                          match uu____25769 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25800 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25829  ->
                                        fun decl  ->
                                          match uu____25829 with
                                          | (env2,out) ->
                                              let uu____25849 =
                                                desugar_decl env2 decl  in
                                              (match uu____25849 with
                                               | (env3,ses) ->
                                                   let uu____25862 =
                                                     let uu____25865 =
                                                       FStar_List.hd ses  in
                                                     uu____25865 :: out  in
                                                   (env3, uu____25862)))
                                     (env1, []))
                                 in
                              (match uu____25800 with
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
                                                 (uu____25911,uu____25912,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25915,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25916,(def,uu____25918)::
                                                        (cps_type,uu____25920)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25921;
                                                     FStar_Parser_AST.level =
                                                       uu____25922;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25955 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25955 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25987 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25988 =
                                                        let uu____25989 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25989
                                                         in
                                                      let uu____25996 =
                                                        let uu____25997 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25997
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25987;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25988;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25996
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____26004,uu____26005,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____26008,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26024 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26024 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26056 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26057 =
                                                        let uu____26058 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26058
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26056;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26057;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26065 ->
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
                                       let uu____26084 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26084
                                        in
                                     let uu____26086 =
                                       let uu____26087 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26087
                                        in
                                     ([], uu____26086)  in
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
                                       let uu____26109 =
                                         let uu____26110 =
                                           let uu____26113 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26113
                                            in
                                         let uu____26115 =
                                           let uu____26118 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26118
                                            in
                                         let uu____26120 =
                                           let uu____26123 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26123
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
                                             uu____26110;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26115;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26120
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26109
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26157 =
                                            match uu____26157 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26204 =
                                            let uu____26205 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26207 =
                                              let uu____26212 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26212 to_comb
                                               in
                                            let uu____26230 =
                                              let uu____26235 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26235 to_comb
                                               in
                                            let uu____26253 =
                                              let uu____26258 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26258 to_comb
                                               in
                                            let uu____26276 =
                                              let uu____26281 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26281 to_comb
                                               in
                                            let uu____26299 =
                                              let uu____26304 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26304 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26205;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26207;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26230;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26253;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26276;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26299
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26204)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26327  ->
                                                 match uu___27_26327 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26330 -> true
                                                 | uu____26332 -> false)
                                              qualifiers
                                             in
                                          let uu____26334 =
                                            let uu____26335 =
                                              lookup "return_wp"  in
                                            let uu____26337 =
                                              lookup "bind_wp"  in
                                            let uu____26339 =
                                              lookup "stronger"  in
                                            let uu____26341 =
                                              lookup "if_then_else"  in
                                            let uu____26343 = lookup "ite_wp"
                                               in
                                            let uu____26345 =
                                              lookup "close_wp"  in
                                            let uu____26347 =
                                              lookup "trivial"  in
                                            let uu____26349 =
                                              if rr
                                              then
                                                let uu____26355 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26355
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26359 =
                                              if rr
                                              then
                                                let uu____26365 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26365
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26369 =
                                              if rr
                                              then
                                                let uu____26375 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26375
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26335;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26337;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26339;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26341;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26343;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26345;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26347;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26349;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26359;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26369
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26334)
                                      in
                                   let sigel =
                                     let uu____26380 =
                                       let uu____26381 =
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
                                           uu____26381
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26380
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
                                               let uu____26398 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26398) env3)
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
                let uu____26421 = desugar_binders env1 eff_binders  in
                match uu____26421 with
                | (env2,binders) ->
                    let uu____26458 =
                      let uu____26469 = head_and_args defn  in
                      match uu____26469 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26506 ->
                                let uu____26507 =
                                  let uu____26513 =
                                    let uu____26515 =
                                      let uu____26517 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26517 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26515  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26513)
                                   in
                                FStar_Errors.raise_error uu____26507
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26523 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26553)::args_rev ->
                                let uu____26565 =
                                  let uu____26566 = unparen last_arg  in
                                  uu____26566.FStar_Parser_AST.tm  in
                                (match uu____26565 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26594 -> ([], args))
                            | uu____26603 -> ([], args)  in
                          (match uu____26523 with
                           | (cattributes,args1) ->
                               let uu____26646 = desugar_args env2 args1  in
                               let uu____26647 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26646, uu____26647))
                       in
                    (match uu____26458 with
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
                          (let uu____26687 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26687 with
                           | (ed_binders,uu____26701,ed_binders_opening) ->
                               let sub' shift_n uu____26720 =
                                 match uu____26720 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26735 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26735 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26739 =
                                       let uu____26740 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26740)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26739
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26761 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26762 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26763 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26779 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26780 =
                                          let uu____26781 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26781
                                           in
                                        let uu____26796 =
                                          let uu____26797 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26797
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26779;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26780;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26796
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
                                     uu____26761;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26762;
                                   FStar_Syntax_Syntax.actions = uu____26763;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26813 =
                                   let uu____26816 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26816 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26813;
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
                                           let uu____26831 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26831) env3)
                                  in
                               let env5 =
                                 let uu____26833 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26833
                                 then
                                   let reflect_lid =
                                     let uu____26840 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26840
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
             let uu____26873 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26873) ats
         in
      let env0 =
        let uu____26894 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26894 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26909 =
        let uu____26916 = get_fail_attr false attrs  in
        match uu____26916 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3413_26953 = d  in
              {
                FStar_Parser_AST.d = (uu___3413_26953.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3413_26953.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3413_26953.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26954 =
              FStar_Errors.catch_errors
                (fun uu____26972  ->
                   FStar_Options.with_saved_options
                     (fun uu____26978  -> desugar_decl_noattrs env d1))
               in
            (match uu____26954 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3428_27038 = se  in
                             let uu____27039 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3428_27038.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3428_27038.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3428_27038.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3428_27038.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27039;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3428_27038.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____27092 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27092 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27141 =
                                 let uu____27147 =
                                   let uu____27149 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27152 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27155 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27157 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27159 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27149 uu____27152 uu____27155
                                     uu____27157 uu____27159
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27147)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27141);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26909 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27197;
                FStar_Syntax_Syntax.sigrng = uu____27198;
                FStar_Syntax_Syntax.sigquals = uu____27199;
                FStar_Syntax_Syntax.sigmeta = uu____27200;
                FStar_Syntax_Syntax.sigattrs = uu____27201;
                FStar_Syntax_Syntax.sigopts = uu____27202;_}::[] ->
                let uu____27215 =
                  let uu____27218 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27218  in
                FStar_All.pipe_right uu____27215
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27226 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27226))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27239;
                FStar_Syntax_Syntax.sigrng = uu____27240;
                FStar_Syntax_Syntax.sigquals = uu____27241;
                FStar_Syntax_Syntax.sigmeta = uu____27242;
                FStar_Syntax_Syntax.sigattrs = uu____27243;
                FStar_Syntax_Syntax.sigopts = uu____27244;_}::uu____27245 ->
                let uu____27270 =
                  let uu____27273 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27273  in
                FStar_All.pipe_right uu____27270
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27281 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27281))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27297;
                FStar_Syntax_Syntax.sigquals = uu____27298;
                FStar_Syntax_Syntax.sigmeta = uu____27299;
                FStar_Syntax_Syntax.sigattrs = uu____27300;
                FStar_Syntax_Syntax.sigopts = uu____27301;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27322 -> []  in
          let attrs1 =
            let uu____27328 = val_attrs sigelts  in
            FStar_List.append attrs uu____27328  in
          let uu____27331 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3488_27335 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3488_27335.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3488_27335.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3488_27335.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3488_27335.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3488_27335.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27331)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27342 = desugar_decl_aux env d  in
      match uu____27342 with
      | (env1,ses) ->
          let uu____27353 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27353)

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
          let uu____27385 = FStar_Syntax_DsEnv.iface env  in
          if uu____27385
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27400 =
               let uu____27402 =
                 let uu____27404 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27405 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27404
                   uu____27405
                  in
               Prims.op_Negation uu____27402  in
             if uu____27400
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27419 =
                  let uu____27421 =
                    let uu____27423 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27423 lid  in
                  Prims.op_Negation uu____27421  in
                if uu____27419
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27437 =
                     let uu____27439 =
                       let uu____27441 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27441
                         lid
                        in
                     Prims.op_Negation uu____27439  in
                   if uu____27437
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27459 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27459, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27488)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27507 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27516 =
            let uu____27521 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27521 tcs  in
          (match uu____27516 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27538 =
                   let uu____27539 =
                     let uu____27546 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27546  in
                   [uu____27539]  in
                 let uu____27559 =
                   let uu____27562 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27565 =
                     let uu____27576 =
                       let uu____27585 =
                         let uu____27586 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27586  in
                       FStar_Syntax_Syntax.as_arg uu____27585  in
                     [uu____27576]  in
                   FStar_Syntax_Util.mk_app uu____27562 uu____27565  in
                 FStar_Syntax_Util.abs uu____27538 uu____27559
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27626,id))::uu____27628 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27631::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27635 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27635 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27641 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27641]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27662) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27672,uu____27673,uu____27674,uu____27675,uu____27676)
                     ->
                     let uu____27685 =
                       let uu____27686 =
                         let uu____27687 =
                           let uu____27694 = mkclass lid  in
                           (meths, uu____27694)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27687  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27686;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27685]
                 | uu____27697 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27731;
                    FStar_Parser_AST.prange = uu____27732;_},uu____27733)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27743;
                    FStar_Parser_AST.prange = uu____27744;_},uu____27745)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27761;
                         FStar_Parser_AST.prange = uu____27762;_},uu____27763);
                    FStar_Parser_AST.prange = uu____27764;_},uu____27765)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27787;
                         FStar_Parser_AST.prange = uu____27788;_},uu____27789);
                    FStar_Parser_AST.prange = uu____27790;_},uu____27791)::[]
                   -> false
               | (p,uu____27820)::[] ->
                   let uu____27829 = is_app_pattern p  in
                   Prims.op_Negation uu____27829
               | uu____27831 -> false)
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
            let uu____27906 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27906 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27919 =
                     let uu____27920 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27920.FStar_Syntax_Syntax.n  in
                   match uu____27919 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27930) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27961 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27986  ->
                                match uu____27986 with
                                | (qs,ats) ->
                                    let uu____28013 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____28013 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27961 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28067::uu____28068 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28071 -> val_quals  in
                            let quals2 =
                              let uu____28075 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28108  ->
                                        match uu____28108 with
                                        | (uu____28122,(uu____28123,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28075
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28143 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28143
                              then
                                let uu____28149 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3665_28164 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3667_28166 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3667_28166.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3667_28166.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3665_28164.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28149)
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
                   | uu____28191 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28199 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28218 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28199 with
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
                       let uu___3690_28255 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3690_28255.FStar_Parser_AST.prange)
                       }
                   | uu____28262 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3694_28269 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3694_28269.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3694_28269.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28285 =
                     let uu____28286 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28286  in
                   FStar_Parser_AST.mk_term uu____28285
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28310 id_opt =
                   match uu____28310 with
                   | (env1,ses) ->
                       let uu____28332 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28344 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28344
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28346 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28346
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
                               let uu____28352 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28352
                                in
                             let bv_pat1 =
                               let uu____28356 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28356
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28332 with
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
                            let uu____28417 = desugar_decl env1 id_decl  in
                            (match uu____28417 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28453 id =
                   match uu____28453 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28492 =
                   match uu____28492 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28516 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28516 FStar_Util.set_elements
                    in
                 let uu____28523 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28526 = is_var_pattern pat  in
                      Prims.op_Negation uu____28526)
                    in
                 if uu____28523
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
            let uu____28550 = close_fun env t  in
            desugar_term env uu____28550  in
          let quals1 =
            let uu____28554 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28554
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28566 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28566;
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
                let uu____28579 =
                  let uu____28588 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28588]  in
                let uu____28607 =
                  let uu____28610 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28610
                   in
                FStar_Syntax_Util.arrow uu____28579 uu____28607
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
          uu____28673) ->
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
          let uu____28690 =
            let uu____28692 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28692  in
          if uu____28690
          then
            let uu____28699 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28717 =
                    let uu____28720 =
                      let uu____28721 = desugar_term env t  in
                      ([], uu____28721)  in
                    FStar_Pervasives_Native.Some uu____28720  in
                  (uu____28717, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28734 =
                    let uu____28737 =
                      let uu____28738 = desugar_term env wp  in
                      ([], uu____28738)  in
                    FStar_Pervasives_Native.Some uu____28737  in
                  let uu____28745 =
                    let uu____28748 =
                      let uu____28749 = desugar_term env t  in
                      ([], uu____28749)  in
                    FStar_Pervasives_Native.Some uu____28748  in
                  (uu____28734, uu____28745)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28761 =
                    let uu____28764 =
                      let uu____28765 = desugar_term env t  in
                      ([], uu____28765)  in
                    FStar_Pervasives_Native.Some uu____28764  in
                  (FStar_Pervasives_Native.None, uu____28761)
               in
            (match uu____28699 with
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
                   let uu____28799 =
                     let uu____28802 =
                       let uu____28803 = desugar_term env t  in
                       ([], uu____28803)  in
                     FStar_Pervasives_Native.Some uu____28802  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28799
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
             | uu____28810 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28823 =
            let uu____28824 =
              let uu____28825 =
                let uu____28826 =
                  let uu____28837 =
                    let uu____28838 = desugar_term env bind  in
                    ([], uu____28838)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28837,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28826  in
              {
                FStar_Syntax_Syntax.sigel = uu____28825;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28824]  in
          (env, uu____28823)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28857 =
              let uu____28858 =
                let uu____28865 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28865, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28858  in
            {
              FStar_Syntax_Syntax.sigel = uu____28857;
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
      let uu____28892 =
        FStar_List.fold_left
          (fun uu____28912  ->
             fun d  ->
               match uu____28912 with
               | (env1,sigelts) ->
                   let uu____28932 = desugar_decl env1 d  in
                   (match uu____28932 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28892 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29023) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29027;
               FStar_Syntax_Syntax.exports = uu____29028;
               FStar_Syntax_Syntax.is_interface = uu____29029;_},FStar_Parser_AST.Module
             (current_lid,uu____29031)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29040) ->
              let uu____29043 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29043
           in
        let uu____29048 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29090 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29090, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29112 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29112, mname, decls, false)
           in
        match uu____29048 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29154 = desugar_decls env2 decls  in
            (match uu____29154 with
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
          let uu____29222 =
            (FStar_Options.interactive ()) &&
              (let uu____29225 =
                 let uu____29227 =
                   let uu____29229 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29229  in
                 FStar_Util.get_file_extension uu____29227  in
               FStar_List.mem uu____29225 ["fsti"; "fsi"])
             in
          if uu____29222 then as_interface m else m  in
        let uu____29243 = desugar_modul_common curmod env m1  in
        match uu____29243 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29265 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29265, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29287 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29287 with
      | (env1,modul,pop_when_done) ->
          let uu____29304 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29304 with
           | (env2,modul1) ->
               ((let uu____29316 =
                   let uu____29318 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29318  in
                 if uu____29316
                 then
                   let uu____29321 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29321
                 else ());
                (let uu____29326 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29326, modul1))))
  
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
        (fun uu____29376  ->
           let uu____29377 = desugar_modul env modul  in
           match uu____29377 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29415  ->
           let uu____29416 = desugar_decls env decls  in
           match uu____29416 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29467  ->
             let uu____29468 = desugar_partial_modul modul env a_modul  in
             match uu____29468 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29563 ->
                  let t =
                    let uu____29573 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29573  in
                  let uu____29586 =
                    let uu____29587 = FStar_Syntax_Subst.compress t  in
                    uu____29587.FStar_Syntax_Syntax.n  in
                  (match uu____29586 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29599,uu____29600)
                       -> bs1
                   | uu____29625 -> failwith "Impossible")
               in
            let uu____29635 =
              let uu____29642 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29642
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29635 with
            | (binders,uu____29644,binders_opening) ->
                let erase_term t =
                  let uu____29652 =
                    let uu____29653 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29653  in
                  FStar_Syntax_Subst.close binders uu____29652  in
                let erase_tscheme uu____29671 =
                  match uu____29671 with
                  | (us,t) ->
                      let t1 =
                        let uu____29691 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29691 t  in
                      let uu____29694 =
                        let uu____29695 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29695  in
                      ([], uu____29694)
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
                    | uu____29718 ->
                        let bs =
                          let uu____29728 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29728  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29768 =
                          let uu____29769 =
                            let uu____29772 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29772  in
                          uu____29769.FStar_Syntax_Syntax.n  in
                        (match uu____29768 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29774,uu____29775) -> bs1
                         | uu____29800 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29808 =
                      let uu____29809 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29809  in
                    FStar_Syntax_Subst.close binders uu____29808  in
                  let uu___3990_29810 = action  in
                  let uu____29811 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29812 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3990_29810.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3990_29810.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29811;
                    FStar_Syntax_Syntax.action_typ = uu____29812
                  }  in
                let uu___3992_29813 = ed  in
                let uu____29814 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29815 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29816 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29817 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3992_29813.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3992_29813.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29814;
                  FStar_Syntax_Syntax.signature = uu____29815;
                  FStar_Syntax_Syntax.combinators = uu____29816;
                  FStar_Syntax_Syntax.actions = uu____29817;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3992_29813.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3999_29833 = se  in
                  let uu____29834 =
                    let uu____29835 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29835  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29834;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3999_29833.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3999_29833.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3999_29833.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3999_29833.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3999_29833.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29837 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29838 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29838 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29855 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29855
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29857 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29857)
  