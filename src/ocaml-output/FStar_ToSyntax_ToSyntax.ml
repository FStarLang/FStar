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
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3707)) ->
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
             let uu____3798 = sum_to_universe u n  in
             FStar_Util.Inr uu____3798
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3815 = sum_to_universe u n  in
             FStar_Util.Inr uu____3815
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3831 =
               let uu____3837 =
                 let uu____3839 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3839
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3837)
                in
             FStar_Errors.raise_error uu____3831 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3848 ->
        let rec aux t1 univargs =
          let uu____3885 =
            let uu____3886 = unparen t1  in uu____3886.FStar_Parser_AST.tm
             in
          match uu____3885 with
          | FStar_Parser_AST.App (t2,targ,uu____3894) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3921  ->
                     match uu___5_3921 with
                     | FStar_Util.Inr uu____3928 -> true
                     | uu____3931 -> false) univargs
              then
                let uu____3939 =
                  let uu____3940 =
                    FStar_List.map
                      (fun uu___6_3950  ->
                         match uu___6_3950 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3940  in
                FStar_Util.Inr uu____3939
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3976  ->
                        match uu___7_3976 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3986 -> failwith "impossible")
                     univargs
                    in
                 let uu____3990 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3990)
          | uu____4006 ->
              let uu____4007 =
                let uu____4013 =
                  let uu____4015 =
                    let uu____4017 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4017 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4015  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4013)  in
              FStar_Errors.raise_error uu____4007 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4032 ->
        let uu____4033 =
          let uu____4039 =
            let uu____4041 =
              let uu____4043 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4043 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4041  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4039)  in
        FStar_Errors.raise_error uu____4033 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4084;_});
            FStar_Syntax_Syntax.pos = uu____4085;
            FStar_Syntax_Syntax.vars = uu____4086;_})::uu____4087
        ->
        let uu____4118 =
          let uu____4124 =
            let uu____4126 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4126
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4124)  in
        FStar_Errors.raise_error uu____4118 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4132 ->
        let uu____4151 =
          let uu____4157 =
            let uu____4159 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4159
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4157)  in
        FStar_Errors.raise_error uu____4151 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4172 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4172) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4200 = FStar_List.hd fields  in
        match uu____4200 with
        | (f,uu____4210) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4221 =
              match uu____4221 with
              | (f',uu____4227) ->
                  let uu____4228 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4228
                  then ()
                  else
                    (let msg =
                       let uu____4235 = FStar_Ident.string_of_lid f  in
                       let uu____4237 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4239 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4235 uu____4237 uu____4239
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4244 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4244);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4292 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4299 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4300 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4302,pats1) ->
            let aux out uu____4343 =
              match uu____4343 with
              | (p1,uu____4356) ->
                  let intersection =
                    let uu____4366 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4366 out  in
                  let uu____4369 = FStar_Util.set_is_empty intersection  in
                  if uu____4369
                  then
                    let uu____4374 = pat_vars p1  in
                    FStar_Util.set_union out uu____4374
                  else
                    (let duplicate_bv =
                       let uu____4380 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4380  in
                     let uu____4383 =
                       let uu____4389 =
                         let uu____4391 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4391
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4389)
                        in
                     FStar_Errors.raise_error uu____4383 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4415 = pat_vars p  in
          FStar_All.pipe_right uu____4415 (fun uu____4420  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4444 =
              let uu____4446 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4446  in
            if uu____4444
            then ()
            else
              (let nonlinear_vars =
                 let uu____4455 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4455  in
               let first_nonlinear_var =
                 let uu____4459 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4459  in
               let uu____4462 =
                 let uu____4468 =
                   let uu____4470 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4470
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4468)  in
               FStar_Errors.raise_error uu____4462 r)
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
          let uu____4797 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4804 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4806 = FStar_Ident.text_of_id x  in
                 uu____4804 = uu____4806) l
             in
          match uu____4797 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4820 ->
              let uu____4823 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4823 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4964 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4986 =
                  let uu____4992 =
                    let uu____4994 = FStar_Ident.text_of_id op  in
                    let uu____4996 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4994
                      uu____4996
                     in
                  let uu____4998 = FStar_Ident.range_of_id op  in
                  (uu____4992, uu____4998)  in
                FStar_Ident.mk_ident uu____4986  in
              let p2 =
                let uu___934_5001 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_5001.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5018 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5021 = aux loc env1 p2  in
                match uu____5021 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5077 =
                      match binder with
                      | LetBinder uu____5098 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5123 = close_fun env1 t  in
                            desugar_term env1 uu____5123  in
                          let x1 =
                            let uu___960_5125 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5125.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5125.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5077 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5171 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5172 -> ()
                           | uu____5173 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5174 ->
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
              let uu____5192 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5192, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5205 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5205, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5223 = resolvex loc env1 x  in
              (match uu____5223 with
               | (loc1,env2,xbv) ->
                   let uu____5255 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5255, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5273 = resolvex loc env1 x  in
              (match uu____5273 with
               | (loc1,env2,xbv) ->
                   let uu____5305 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5305, []))
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
              let uu____5319 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5319, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5347;_},args)
              ->
              let uu____5353 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5414  ->
                       match uu____5414 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5495 = aux loc1 env2 arg  in
                           (match uu____5495 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5353 with
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
                   let uu____5667 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5667, annots))
          | FStar_Parser_AST.PatApp uu____5683 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5711 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5761  ->
                       match uu____5761 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5822 = aux loc1 env2 pat  in
                           (match uu____5822 with
                            | (loc2,env3,uu____5861,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5711 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5955 =
                       let uu____5958 =
                         let uu____5965 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5965  in
                       let uu____5966 =
                         let uu____5967 =
                           let uu____5981 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5981, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5967  in
                       FStar_All.pipe_left uu____5958 uu____5966  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6015 =
                              let uu____6016 =
                                let uu____6030 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6030, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6016  in
                            FStar_All.pipe_left (pos_r r) uu____6015) pats1
                       uu____5955
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
              let uu____6086 =
                FStar_List.fold_left
                  (fun uu____6145  ->
                     fun p2  ->
                       match uu____6145 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6227 = aux loc1 env2 p2  in
                           (match uu____6227 with
                            | (loc2,env3,uu____6271,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6086 with
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
                     | uu____6434 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6437 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6437, annots))
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
                     (fun uu____6514  ->
                        match uu____6514 with
                        | (f,p2) ->
                            let uu____6525 = FStar_Ident.ident_of_lid f  in
                            (uu____6525, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6545  ->
                        match uu____6545 with
                        | (f,uu____6551) ->
                            let uu____6552 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6580  ->
                                      match uu____6580 with
                                      | (g,uu____6587) ->
                                          let uu____6588 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6590 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6588 = uu____6590))
                               in
                            (match uu____6552 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6597,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6604 =
                  let uu____6605 =
                    let uu____6612 =
                      let uu____6613 =
                        let uu____6614 =
                          let uu____6615 =
                            let uu____6616 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6616
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6615  in
                        FStar_Parser_AST.PatName uu____6614  in
                      FStar_Parser_AST.mk_pattern uu____6613
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6612, args)  in
                  FStar_Parser_AST.PatApp uu____6605  in
                FStar_Parser_AST.mk_pattern uu____6604
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6621 = aux loc env1 app  in
              (match uu____6621 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6698 =
                           let uu____6699 =
                             let uu____6713 =
                               let uu___1110_6714 = fv  in
                               let uu____6715 =
                                 let uu____6718 =
                                   let uu____6719 =
                                     let uu____6726 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6726)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6719
                                    in
                                 FStar_Pervasives_Native.Some uu____6718  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6714.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6714.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6715
                               }  in
                             (uu____6713, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6699  in
                         FStar_All.pipe_left pos uu____6698
                     | uu____6752 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6836 = aux' true loc env1 p2  in
              (match uu____6836 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6889 =
                     FStar_List.fold_left
                       (fun uu____6937  ->
                          fun p4  ->
                            match uu____6937 with
                            | (loc2,env3,ps1) ->
                                let uu____7002 = aux' true loc2 env3 p4  in
                                (match uu____7002 with
                                 | (loc3,env4,uu____7040,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6889 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7201 ->
              let uu____7202 = aux' true loc env1 p1  in
              (match uu____7202 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7293 = aux_maybe_or env p  in
        match uu____7293 with
        | (env1,b,pats) ->
            ((let uu____7348 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7348
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
            let uu____7422 =
              let uu____7423 =
                let uu____7434 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7434, (ty, tacopt))  in
              LetBinder uu____7423  in
            (env, uu____7422, [])  in
          let op_to_ident x =
            let uu____7451 =
              let uu____7457 =
                let uu____7459 = FStar_Ident.text_of_id x  in
                let uu____7461 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7459
                  uu____7461
                 in
              let uu____7463 = FStar_Ident.range_of_id x  in
              (uu____7457, uu____7463)  in
            FStar_Ident.mk_ident uu____7451  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7474 = op_to_ident x  in
              mklet uu____7474 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7476) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7482;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7498 = op_to_ident x  in
              let uu____7499 = desugar_term env t  in
              mklet uu____7498 uu____7499 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7501);
                 FStar_Parser_AST.prange = uu____7502;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7522 = desugar_term env t  in
              mklet x uu____7522 tacopt1
          | uu____7523 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7536 = desugar_data_pat true env p  in
           match uu____7536 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7566;
                      FStar_Syntax_Syntax.p = uu____7567;_},uu____7568)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7581;
                      FStar_Syntax_Syntax.p = uu____7582;_},uu____7583)::[]
                     -> []
                 | uu____7596 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7604  ->
    fun env  ->
      fun pat  ->
        let uu____7608 = desugar_data_pat false env pat  in
        match uu____7608 with | (env1,uu____7625,pat1) -> (env1, pat1)

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
      let uu____7647 = desugar_term_aq env e  in
      match uu____7647 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7666 = desugar_typ_aq env e  in
      match uu____7666 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7676  ->
        fun range  ->
          match uu____7676 with
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
              ((let uu____7698 =
                  let uu____7700 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7700  in
                if uu____7698
                then
                  let uu____7703 =
                    let uu____7709 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7709)  in
                  FStar_Errors.log_issue range uu____7703
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
                  let uu____7730 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7730 range  in
                let lid1 =
                  let uu____7734 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7734 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7744 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7744 range  in
                           let private_fv =
                             let uu____7746 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7746 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7747 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7747.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7747.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7748 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7752 =
                        let uu____7758 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7758)
                         in
                      FStar_Errors.raise_error uu____7752 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7778 =
                  let uu____7785 =
                    let uu____7786 =
                      let uu____7803 =
                        let uu____7814 =
                          let uu____7823 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7823)  in
                        [uu____7814]  in
                      (lid1, uu____7803)  in
                    FStar_Syntax_Syntax.Tm_app uu____7786  in
                  FStar_Syntax_Syntax.mk uu____7785  in
                uu____7778 FStar_Pervasives_Native.None range))

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
          let uu___1293_7942 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7942.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7942.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7945 =
          let uu____7946 = unparen top  in uu____7946.FStar_Parser_AST.tm  in
        match uu____7945 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7951 ->
            let uu____7960 = desugar_formula env top  in (uu____7960, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7969 = desugar_formula env t  in (uu____7969, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7978 = desugar_formula env t  in (uu____7978, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8005 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8005, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8007 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8007, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8014 = FStar_Ident.text_of_id id  in uu____8014 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8020 =
                let uu____8021 =
                  let uu____8028 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8028, args)  in
                FStar_Parser_AST.Op uu____8021  in
              FStar_Parser_AST.mk_term uu____8020 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8033 =
              let uu____8034 =
                let uu____8035 =
                  let uu____8042 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8042, [e])  in
                FStar_Parser_AST.Op uu____8035  in
              FStar_Parser_AST.mk_term uu____8034 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8033
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8054 = FStar_Ident.text_of_id op_star  in
             uu____8054 = "*") &&
              (let uu____8059 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8059 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8083 = FStar_Ident.text_of_id id  in
                   uu____8083 = "*") &&
                    (let uu____8088 =
                       op_as_term env (Prims.of_int (2))
                         top.FStar_Parser_AST.range op_star
                        in
                     FStar_All.pipe_right uu____8088 FStar_Option.isNone)
                  ->
                  let uu____8095 = flatten t1  in
                  FStar_List.append uu____8095 [t2]
              | uu____8098 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1338_8103 = top  in
              let uu____8104 =
                let uu____8105 =
                  let uu____8116 =
                    FStar_List.map
                      (fun uu____8127  -> FStar_Util.Inr uu____8127) terms
                     in
                  (uu____8116, rhs)  in
                FStar_Parser_AST.Sum uu____8105  in
              {
                FStar_Parser_AST.tm = uu____8104;
                FStar_Parser_AST.range =
                  (uu___1338_8103.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1338_8103.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8135 =
              let uu____8136 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8136  in
            (uu____8135, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8142 =
              let uu____8148 =
                let uu____8150 =
                  let uu____8152 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8152 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8150  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8148)  in
            FStar_Errors.raise_error uu____8142 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8167 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8167 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8174 =
                   let uu____8180 =
                     let uu____8182 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8182
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8180)
                    in
                 FStar_Errors.raise_error uu____8174
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8197 =
                     let uu____8222 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8284 = desugar_term_aq env t  in
                               match uu____8284 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8222 FStar_List.unzip  in
                   (match uu____8197 with
                    | (args1,aqs) ->
                        let uu____8417 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8417, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8434)::[]) when
            let uu____8449 = FStar_Ident.string_of_lid n  in
            uu____8449 = "SMTPat" ->
            let uu____8453 =
              let uu___1367_8454 = top  in
              let uu____8455 =
                let uu____8456 =
                  let uu____8463 =
                    let uu___1369_8464 = top  in
                    let uu____8465 =
                      let uu____8466 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8466  in
                    {
                      FStar_Parser_AST.tm = uu____8465;
                      FStar_Parser_AST.range =
                        (uu___1369_8464.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1369_8464.FStar_Parser_AST.level)
                    }  in
                  (uu____8463, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8456  in
              {
                FStar_Parser_AST.tm = uu____8455;
                FStar_Parser_AST.range =
                  (uu___1367_8454.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1367_8454.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8453
        | FStar_Parser_AST.Construct (n,(a,uu____8469)::[]) when
            let uu____8484 = FStar_Ident.string_of_lid n  in
            uu____8484 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8491 =
                let uu___1379_8492 = top  in
                let uu____8493 =
                  let uu____8494 =
                    let uu____8501 =
                      let uu___1381_8502 = top  in
                      let uu____8503 =
                        let uu____8504 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8504  in
                      {
                        FStar_Parser_AST.tm = uu____8503;
                        FStar_Parser_AST.range =
                          (uu___1381_8502.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1381_8502.FStar_Parser_AST.level)
                      }  in
                    (uu____8501, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8494  in
                {
                  FStar_Parser_AST.tm = uu____8493;
                  FStar_Parser_AST.range =
                    (uu___1379_8492.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1379_8492.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8491))
        | FStar_Parser_AST.Construct (n,(a,uu____8507)::[]) when
            let uu____8522 = FStar_Ident.string_of_lid n  in
            uu____8522 = "SMTPatOr" ->
            let uu____8526 =
              let uu___1390_8527 = top  in
              let uu____8528 =
                let uu____8529 =
                  let uu____8536 =
                    let uu___1392_8537 = top  in
                    let uu____8538 =
                      let uu____8539 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8539  in
                    {
                      FStar_Parser_AST.tm = uu____8538;
                      FStar_Parser_AST.range =
                        (uu___1392_8537.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1392_8537.FStar_Parser_AST.level)
                    }  in
                  (uu____8536, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8529  in
              {
                FStar_Parser_AST.tm = uu____8528;
                FStar_Parser_AST.range =
                  (uu___1390_8527.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1390_8527.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8526
        | FStar_Parser_AST.Name lid when
            let uu____8541 = FStar_Ident.string_of_lid lid  in
            uu____8541 = "Type0" ->
            let uu____8545 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8545, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8547 = FStar_Ident.string_of_lid lid  in
            uu____8547 = "Type" ->
            let uu____8551 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8551, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8568 = FStar_Ident.string_of_lid lid  in
            uu____8568 = "Type" ->
            let uu____8572 =
              let uu____8573 =
                let uu____8574 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8574  in
              mk uu____8573  in
            (uu____8572, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8576 = FStar_Ident.string_of_lid lid  in
            uu____8576 = "Effect" ->
            let uu____8580 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8580, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8582 = FStar_Ident.string_of_lid lid  in
            uu____8582 = "True" ->
            let uu____8586 =
              let uu____8587 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8587
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8586, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8589 = FStar_Ident.string_of_lid lid  in
            uu____8589 = "False" ->
            let uu____8593 =
              let uu____8594 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8594
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8593, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8599 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8599) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8603 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8603 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8612 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8612, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8614 =
                   let uu____8616 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8616 txt
                    in
                 failwith uu____8614)
        | FStar_Parser_AST.Var l ->
            let uu____8624 = desugar_name mk setpos env true l  in
            (uu____8624, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8632 = desugar_name mk setpos env true l  in
            (uu____8632, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8649 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8649 with
              | FStar_Pervasives_Native.Some uu____8659 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8667 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8667 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8685 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8706 =
                   let uu____8707 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8707  in
                 (uu____8706, noaqs)
             | uu____8713 ->
                 let uu____8721 =
                   let uu____8727 =
                     let uu____8729 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8729
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8727)  in
                 FStar_Errors.raise_error uu____8721
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8738 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8738 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8745 =
                   let uu____8751 =
                     let uu____8753 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8753
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8751)
                    in
                 FStar_Errors.raise_error uu____8745
                   top.FStar_Parser_AST.range
             | uu____8761 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8765 = desugar_name mk setpos env true lid'  in
                 (uu____8765, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8786 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8786 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8805 ->
                      let uu____8812 =
                        FStar_Util.take
                          (fun uu____8836  ->
                             match uu____8836 with
                             | (uu____8842,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8812 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8887 =
                             let uu____8912 =
                               FStar_List.map
                                 (fun uu____8955  ->
                                    match uu____8955 with
                                    | (t,imp) ->
                                        let uu____8972 =
                                          desugar_term_aq env t  in
                                        (match uu____8972 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8912 FStar_List.unzip
                              in
                           (match uu____8887 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9115 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9115, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9134 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9134 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9142 =
                         let uu____9144 =
                           let uu____9146 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9146 " not found"  in
                         Prims.op_Hat "Constructor " uu____9144  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9142)
                   | FStar_Pervasives_Native.Some uu____9151 ->
                       let uu____9152 =
                         let uu____9154 =
                           let uu____9156 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9156
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9154  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9152)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9185  ->
                 match uu___8_9185 with
                 | FStar_Util.Inr uu____9191 -> true
                 | uu____9193 -> false) binders
            ->
            let terms =
              let uu____9202 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9219  ->
                        match uu___9_9219 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9225 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9202 [t]  in
            let uu____9227 =
              let uu____9252 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9309 = desugar_typ_aq env t1  in
                        match uu____9309 with
                        | (t',aq) ->
                            let uu____9320 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9320, aq)))
                 in
              FStar_All.pipe_right uu____9252 FStar_List.unzip  in
            (match uu____9227 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9430 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9430
                    in
                 let uu____9439 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9439, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9466 =
              let uu____9483 =
                let uu____9490 =
                  let uu____9497 =
                    FStar_All.pipe_left
                      (fun uu____9506  -> FStar_Util.Inl uu____9506)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9497]  in
                FStar_List.append binders uu____9490  in
              FStar_List.fold_left
                (fun uu____9551  ->
                   fun b  ->
                     match uu____9551 with
                     | (env1,tparams,typs) ->
                         let uu____9612 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9627 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9627)
                            in
                         (match uu____9612 with
                          | (xopt,t1) ->
                              let uu____9652 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9661 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9661)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9652 with
                               | (env2,x) ->
                                   let uu____9681 =
                                     let uu____9684 =
                                       let uu____9687 =
                                         let uu____9688 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9688
                                          in
                                       [uu____9687]  in
                                     FStar_List.append typs uu____9684  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1521_9714 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1521_9714.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1521_9714.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9681)))) (env, [], []) uu____9483
               in
            (match uu____9466 with
             | (env1,uu____9742,targs) ->
                 let tup =
                   let uu____9765 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9765
                    in
                 let uu____9766 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9766, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9785 = uncurry binders t  in
            (match uu____9785 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9829 =
                   match uu___10_9829 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9846 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9846
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9870 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9870 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9903 = aux env [] bs  in (uu____9903, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9912 = desugar_binder env b  in
            (match uu____9912 with
             | (FStar_Pervasives_Native.None ,uu____9923) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9938 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9938 with
                  | ((x,uu____9954),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9967 =
                        let uu____9968 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9968  in
                      (uu____9967, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10046 = FStar_Util.set_is_empty i  in
                    if uu____10046
                    then
                      let uu____10051 = FStar_Util.set_union acc set  in
                      aux uu____10051 sets2
                    else
                      (let uu____10056 =
                         let uu____10057 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10057  in
                       FStar_Pervasives_Native.Some uu____10056)
                 in
              let uu____10060 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10060 sets  in
            ((let uu____10064 = check_disjoint bvss  in
              match uu____10064 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10068 =
                    let uu____10074 =
                      let uu____10076 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10076
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10074)
                     in
                  let uu____10080 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10068 uu____10080);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10088 =
                FStar_List.fold_left
                  (fun uu____10108  ->
                     fun pat  ->
                       match uu____10108 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10134,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10144 =
                                  let uu____10147 = free_type_vars env1 t  in
                                  FStar_List.append uu____10147 ftvs  in
                                (env1, uu____10144)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10152,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10163 =
                                  let uu____10166 = free_type_vars env1 t  in
                                  let uu____10169 =
                                    let uu____10172 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10172 ftvs  in
                                  FStar_List.append uu____10166 uu____10169
                                   in
                                (env1, uu____10163)
                            | uu____10177 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10088 with
              | (uu____10186,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10198 =
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
                    FStar_List.append uu____10198 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10278 = desugar_term_aq env1 body  in
                        (match uu____10278 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10313 =
                                       let uu____10314 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10314
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10313
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
                             let uu____10383 =
                               let uu____10384 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10384  in
                             (uu____10383, aq))
                    | p::rest ->
                        let uu____10397 = desugar_binding_pat env1 p  in
                        (match uu____10397 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10429)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10444 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10453 =
                               match b with
                               | LetBinder uu____10494 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10563) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10617 =
                                           let uu____10626 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10626, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10617
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10688,uu____10689) ->
                                              let tup2 =
                                                let uu____10691 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10691
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10696 =
                                                  let uu____10703 =
                                                    let uu____10704 =
                                                      let uu____10721 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10724 =
                                                        let uu____10735 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10744 =
                                                          let uu____10755 =
                                                            let uu____10764 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10764
                                                             in
                                                          [uu____10755]  in
                                                        uu____10735 ::
                                                          uu____10744
                                                         in
                                                      (uu____10721,
                                                        uu____10724)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10704
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10703
                                                   in
                                                uu____10696
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10812 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10812
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10863,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10865,pats1)) ->
                                              let tupn =
                                                let uu____10910 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10910
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10923 =
                                                  let uu____10924 =
                                                    let uu____10941 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10944 =
                                                      let uu____10955 =
                                                        let uu____10966 =
                                                          let uu____10975 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10975
                                                           in
                                                        [uu____10966]  in
                                                      FStar_List.append args
                                                        uu____10955
                                                       in
                                                    (uu____10941,
                                                      uu____10944)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10924
                                                   in
                                                mk uu____10923  in
                                              let p2 =
                                                let uu____11023 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11023
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11070 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10453 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11162,uu____11163,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11185 =
                let uu____11186 = unparen e  in
                uu____11186.FStar_Parser_AST.tm  in
              match uu____11185 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11196 ->
                  let uu____11197 = desugar_term_aq env e  in
                  (match uu____11197 with
                   | (head,aq) ->
                       let uu____11210 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11210, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11217 ->
            let rec aux args aqs e =
              let uu____11294 =
                let uu____11295 = unparen e  in
                uu____11295.FStar_Parser_AST.tm  in
              match uu____11294 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11313 = desugar_term_aq env t  in
                  (match uu____11313 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11361 ->
                  let uu____11362 = desugar_term_aq env e  in
                  (match uu____11362 with
                   | (head,aq) ->
                       let uu____11383 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11383, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11436 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11436
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11443 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11443  in
            let bind =
              let uu____11448 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11448 FStar_Parser_AST.Expr
               in
            let uu____11449 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11449
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
            let uu____11501 = desugar_term_aq env t  in
            (match uu____11501 with
             | (tm,s) ->
                 let uu____11512 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11512, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11518 =
              let uu____11531 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11531 then desugar_typ_aq else desugar_term_aq  in
            uu____11518 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11598 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11741  ->
                        match uu____11741 with
                        | (attr_opt,(p,def)) ->
                            let uu____11799 = is_app_pattern p  in
                            if uu____11799
                            then
                              let uu____11832 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11832, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11915 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11915, def1)
                               | uu____11960 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11998);
                                           FStar_Parser_AST.prange =
                                             uu____11999;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12048 =
                                            let uu____12069 =
                                              let uu____12074 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12074  in
                                            (uu____12069, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12048, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12166) ->
                                        if top_level
                                        then
                                          let uu____12202 =
                                            let uu____12223 =
                                              let uu____12228 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12228  in
                                            (uu____12223, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12202, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12319 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12352 =
                FStar_List.fold_left
                  (fun uu____12441  ->
                     fun uu____12442  ->
                       match (uu____12441, uu____12442) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12572,uu____12573),uu____12574))
                           ->
                           let uu____12708 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12748 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12748 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12783 =
                                        let uu____12786 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12786 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12783, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12802 =
                                   let uu____12810 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12810
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12802 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12708 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12352 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13056 =
                    match uu____13056 with
                    | (attrs_opt,(uu____13096,args,result_t),def) ->
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
                                let uu____13188 = is_comp_type env1 t  in
                                if uu____13188
                                then
                                  ((let uu____13192 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13202 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13202))
                                       in
                                    match uu____13192 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13209 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13212 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13212))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13209
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
                          | uu____13223 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13226 = desugar_term_aq env1 def2  in
                        (match uu____13226 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13248 =
                                     let uu____13249 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13249
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13248
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
                  let uu____13290 =
                    let uu____13307 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13307 FStar_List.unzip  in
                  (match uu____13290 with
                   | (lbs1,aqss) ->
                       let uu____13449 = desugar_term_aq env' body  in
                       (match uu____13449 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13555  ->
                                    fun used_marker  ->
                                      match uu____13555 with
                                      | (_attr_opt,(f,uu____13629,uu____13630),uu____13631)
                                          ->
                                          let uu____13688 =
                                            let uu____13690 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13690  in
                                          if uu____13688
                                          then
                                            let uu____13714 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13732 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13734 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13732, "Local",
                                                    uu____13734)
                                              | FStar_Util.Inr l ->
                                                  let uu____13739 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13741 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13739, "Global",
                                                    uu____13741)
                                               in
                                            (match uu____13714 with
                                             | (nm,gl,rng) ->
                                                 let uu____13752 =
                                                   let uu____13758 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13758)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13752)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13766 =
                                let uu____13769 =
                                  let uu____13770 =
                                    let uu____13784 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13784)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13770  in
                                FStar_All.pipe_left mk uu____13769  in
                              (uu____13766,
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
              let uu____13886 = desugar_term_aq env t1  in
              match uu____13886 with
              | (t11,aq0) ->
                  let uu____13907 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13907 with
                   | (env1,binder,pat1) ->
                       let uu____13937 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13979 = desugar_term_aq env1 t2  in
                             (match uu____13979 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____14001 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14001
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____14002 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____14002, aq))
                         | LocalBinder (x,uu____14043) ->
                             let uu____14044 = desugar_term_aq env1 t2  in
                             (match uu____14044 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14066;
                                         FStar_Syntax_Syntax.p = uu____14067;_},uu____14068)::[]
                                        -> body1
                                    | uu____14081 ->
                                        let uu____14084 =
                                          let uu____14091 =
                                            let uu____14092 =
                                              let uu____14115 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14118 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14115, uu____14118)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14092
                                             in
                                          FStar_Syntax_Syntax.mk uu____14091
                                           in
                                        uu____14084
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14155 =
                                    let uu____14158 =
                                      let uu____14159 =
                                        let uu____14173 =
                                          let uu____14176 =
                                            let uu____14177 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14177]  in
                                          FStar_Syntax_Subst.close
                                            uu____14176 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14173)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14159
                                       in
                                    FStar_All.pipe_left mk uu____14158  in
                                  (uu____14155, aq))
                          in
                       (match uu____13937 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14285 = FStar_List.hd lbs  in
            (match uu____14285 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14329 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14329
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14345 =
                let uu____14346 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14346  in
              mk uu____14345  in
            let uu____14347 = desugar_term_aq env t1  in
            (match uu____14347 with
             | (t1',aq1) ->
                 let uu____14358 = desugar_term_aq env t2  in
                 (match uu____14358 with
                  | (t2',aq2) ->
                      let uu____14369 = desugar_term_aq env t3  in
                      (match uu____14369 with
                       | (t3',aq3) ->
                           let uu____14380 =
                             let uu____14381 =
                               let uu____14382 =
                                 let uu____14405 =
                                   let uu____14422 =
                                     let uu____14437 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14437,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14451 =
                                     let uu____14468 =
                                       let uu____14483 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14483,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14468]  in
                                   uu____14422 :: uu____14451  in
                                 (t1', uu____14405)  in
                               FStar_Syntax_Syntax.Tm_match uu____14382  in
                             mk uu____14381  in
                           (uu____14380, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14679 =
              match uu____14679 with
              | (pat,wopt,b) ->
                  let uu____14701 = desugar_match_pat env pat  in
                  (match uu____14701 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14732 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14732
                          in
                       let uu____14737 = desugar_term_aq env1 b  in
                       (match uu____14737 with
                        | (b1,aq) ->
                            let uu____14750 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14750, aq)))
               in
            let uu____14755 = desugar_term_aq env e  in
            (match uu____14755 with
             | (e1,aq) ->
                 let uu____14766 =
                   let uu____14797 =
                     let uu____14830 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14830 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14797
                     (fun uu____15048  ->
                        match uu____15048 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14766 with
                  | (brs,aqs) ->
                      let uu____15267 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15267, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15301 =
              let uu____15322 = is_comp_type env t  in
              if uu____15322
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15377 = desugar_term_aq env t  in
                 match uu____15377 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15301 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15469 = desugar_term_aq env e  in
                 (match uu____15469 with
                  | (e1,aq) ->
                      let uu____15480 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15480, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15519,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15562 = FStar_List.hd fields  in
              match uu____15562 with
              | (f,uu____15574) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15622  ->
                        match uu____15622 with
                        | (g,uu____15629) ->
                            let uu____15630 = FStar_Ident.text_of_id f  in
                            let uu____15632 =
                              let uu____15634 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15634  in
                            uu____15630 = uu____15632))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15641,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15655 =
                         let uu____15661 =
                           let uu____15663 = FStar_Ident.text_of_id f  in
                           let uu____15665 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15663 uu____15665
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15661)
                          in
                       FStar_Errors.raise_error uu____15655
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
                  let uu____15676 =
                    let uu____15687 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15718  ->
                              match uu____15718 with
                              | (f,uu____15728) ->
                                  let uu____15729 =
                                    let uu____15730 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15730
                                     in
                                  (uu____15729, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15687)  in
                  FStar_Parser_AST.Construct uu____15676
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15748 =
                      let uu____15749 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15749  in
                    let uu____15750 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15748 uu____15750
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15752 =
                      let uu____15765 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15795  ->
                                match uu____15795 with
                                | (f,uu____15805) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15765)  in
                    FStar_Parser_AST.Record uu____15752  in
                  let uu____15814 =
                    let uu____15835 =
                      let uu____15850 =
                        let uu____15863 =
                          let uu____15868 =
                            let uu____15869 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15869
                             in
                          (uu____15868, e)  in
                        (FStar_Pervasives_Native.None, uu____15863)  in
                      [uu____15850]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15835,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15814
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15921 = desugar_term_aq env recterm1  in
            (match uu____15921 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15937;
                         FStar_Syntax_Syntax.vars = uu____15938;_},args)
                      ->
                      let uu____15964 =
                        let uu____15965 =
                          let uu____15966 =
                            let uu____15983 =
                              let uu____15986 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15987 =
                                let uu____15990 =
                                  let uu____15991 =
                                    let uu____15998 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15998)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15991
                                   in
                                FStar_Pervasives_Native.Some uu____15990  in
                              FStar_Syntax_Syntax.fvar uu____15986
                                FStar_Syntax_Syntax.delta_constant
                                uu____15987
                               in
                            (uu____15983, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15966  in
                        FStar_All.pipe_left mk uu____15965  in
                      (uu____15964, s)
                  | uu____16027 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16030 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16030 with
             | (constrname,is_rec) ->
                 let uu____16049 = desugar_term_aq env e  in
                 (match uu____16049 with
                  | (e1,s) ->
                      let projname =
                        let uu____16061 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16061
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16068 =
                            let uu____16069 =
                              let uu____16074 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16074)  in
                            FStar_Syntax_Syntax.Record_projector uu____16069
                             in
                          FStar_Pervasives_Native.Some uu____16068
                        else FStar_Pervasives_Native.None  in
                      let uu____16077 =
                        let uu____16078 =
                          let uu____16079 =
                            let uu____16096 =
                              let uu____16099 =
                                let uu____16100 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16100
                                 in
                              FStar_Syntax_Syntax.fvar uu____16099
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16102 =
                              let uu____16113 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16113]  in
                            (uu____16096, uu____16102)  in
                          FStar_Syntax_Syntax.Tm_app uu____16079  in
                        FStar_All.pipe_left mk uu____16078  in
                      (uu____16077, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16153 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16153
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16164 =
              let uu____16165 = FStar_Syntax_Subst.compress tm  in
              uu____16165.FStar_Syntax_Syntax.n  in
            (match uu____16164 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16173 =
                   let uu___2089_16174 =
                     let uu____16175 =
                       let uu____16177 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16177  in
                     FStar_Syntax_Util.exp_string uu____16175  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2089_16174.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2089_16174.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16173, noaqs)
             | uu____16178 ->
                 let uu____16179 =
                   let uu____16185 =
                     let uu____16187 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16187
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16185)  in
                 FStar_Errors.raise_error uu____16179
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16196 = desugar_term_aq env e  in
            (match uu____16196 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16208 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16208, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16213 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16214 =
              let uu____16215 =
                let uu____16222 = desugar_term env e  in (bv, uu____16222)
                 in
              [uu____16215]  in
            (uu____16213, uu____16214)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16247 =
              let uu____16248 =
                let uu____16249 =
                  let uu____16256 = desugar_term env e  in (uu____16256, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16249  in
              FStar_All.pipe_left mk uu____16248  in
            (uu____16247, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16285 -> false  in
              let uu____16287 =
                let uu____16288 = unparen rel1  in
                uu____16288.FStar_Parser_AST.tm  in
              match uu____16287 with
              | FStar_Parser_AST.Op (id,uu____16291) ->
                  let uu____16296 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id
                     in
                  (match uu____16296 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16304 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16304 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16315 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16315 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16321 -> false  in
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
              let uu____16342 =
                let uu____16343 =
                  let uu____16350 =
                    let uu____16351 =
                      let uu____16352 =
                        let uu____16361 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16374 =
                          let uu____16375 =
                            let uu____16376 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16376  in
                          FStar_Parser_AST.mk_term uu____16375
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16361, uu____16374,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16352  in
                    FStar_Parser_AST.mk_term uu____16351
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16350)  in
                FStar_Parser_AST.Abs uu____16343  in
              FStar_Parser_AST.mk_term uu____16342
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
              let uu____16397 = FStar_List.last steps  in
              match uu____16397 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16400,uu____16401,last_expr)) -> last_expr
              | uu____16403 -> failwith "impossible: no last_expr on calc"
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
            let uu____16431 =
              FStar_List.fold_left
                (fun uu____16449  ->
                   fun uu____16450  ->
                     match (uu____16449, uu____16450) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16473 = is_impl rel2  in
                           if uu____16473
                           then
                             let uu____16476 =
                               let uu____16483 =
                                 let uu____16488 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16488, FStar_Parser_AST.Nothing)  in
                               [uu____16483]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16476 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16500 =
                             let uu____16507 =
                               let uu____16514 =
                                 let uu____16521 =
                                   let uu____16528 =
                                     let uu____16533 = eta_and_annot rel2  in
                                     (uu____16533, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16534 =
                                     let uu____16541 =
                                       let uu____16548 =
                                         let uu____16553 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16553,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16554 =
                                         let uu____16561 =
                                           let uu____16566 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16566,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16561]  in
                                       uu____16548 :: uu____16554  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16541
                                      in
                                   uu____16528 :: uu____16534  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16521
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16514
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16507
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16500
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16431 with
             | (e1,uu____16604) ->
                 let e2 =
                   let uu____16606 =
                     let uu____16613 =
                       let uu____16620 =
                         let uu____16627 =
                           let uu____16632 = FStar_Parser_AST.thunk e1  in
                           (uu____16632, FStar_Parser_AST.Nothing)  in
                         [uu____16627]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16620  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16613  in
                   FStar_Parser_AST.mkApp finish uu____16606
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16649 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16650 = desugar_formula env top  in
            (uu____16650, noaqs)
        | uu____16651 ->
            let uu____16652 =
              let uu____16658 =
                let uu____16660 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16660  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16658)  in
            FStar_Errors.raise_error uu____16652 top.FStar_Parser_AST.range

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
           (fun uu____16704  ->
              match uu____16704 with
              | (a,imp) ->
                  let uu____16717 = desugar_term env a  in
                  arg_withimp_e imp uu____16717))

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
          let is_requires uu____16754 =
            match uu____16754 with
            | (t1,uu____16761) ->
                let uu____16762 =
                  let uu____16763 = unparen t1  in
                  uu____16763.FStar_Parser_AST.tm  in
                (match uu____16762 with
                 | FStar_Parser_AST.Requires uu____16765 -> true
                 | uu____16774 -> false)
             in
          let is_ensures uu____16786 =
            match uu____16786 with
            | (t1,uu____16793) ->
                let uu____16794 =
                  let uu____16795 = unparen t1  in
                  uu____16795.FStar_Parser_AST.tm  in
                (match uu____16794 with
                 | FStar_Parser_AST.Ensures uu____16797 -> true
                 | uu____16806 -> false)
             in
          let is_app head uu____16824 =
            match uu____16824 with
            | (t1,uu____16832) ->
                let uu____16833 =
                  let uu____16834 = unparen t1  in
                  uu____16834.FStar_Parser_AST.tm  in
                (match uu____16833 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16837;
                        FStar_Parser_AST.level = uu____16838;_},uu____16839,uu____16840)
                     ->
                     let uu____16841 =
                       let uu____16843 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16843  in
                     uu____16841 = head
                 | uu____16845 -> false)
             in
          let is_smt_pat uu____16857 =
            match uu____16857 with
            | (t1,uu____16864) ->
                let uu____16865 =
                  let uu____16866 = unparen t1  in
                  uu____16866.FStar_Parser_AST.tm  in
                (match uu____16865 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16870);
                              FStar_Parser_AST.range = uu____16871;
                              FStar_Parser_AST.level = uu____16872;_},uu____16873)::uu____16874::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16914 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16914 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16926;
                              FStar_Parser_AST.level = uu____16927;_},uu____16928)::uu____16929::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16957 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16957 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16965 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____17000 = head_and_args t1  in
            match uu____17000 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17058 =
                       let uu____17060 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17060  in
                     uu____17058 = "Lemma" ->
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
                     let thunk_ens uu____17096 =
                       match uu____17096 with
                       | (e,i) ->
                           let uu____17107 = FStar_Parser_AST.thunk e  in
                           (uu____17107, i)
                        in
                     let fail_lemma uu____17119 =
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
                           let uu____17225 =
                             let uu____17232 =
                               let uu____17239 = thunk_ens ens  in
                               [uu____17239; nil_pat]  in
                             req_true :: uu____17232  in
                           unit_tm :: uu____17225
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17286 =
                             let uu____17293 =
                               let uu____17300 = thunk_ens ens  in
                               [uu____17300; nil_pat]  in
                             req :: uu____17293  in
                           unit_tm :: uu____17286
                       | ens::smtpat::[] when
                           (((let uu____17349 = is_requires ens  in
                              Prims.op_Negation uu____17349) &&
                               (let uu____17352 = is_smt_pat ens  in
                                Prims.op_Negation uu____17352))
                              &&
                              (let uu____17355 = is_decreases ens  in
                               Prims.op_Negation uu____17355))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17357 =
                             let uu____17364 =
                               let uu____17371 = thunk_ens ens  in
                               [uu____17371; smtpat]  in
                             req_true :: uu____17364  in
                           unit_tm :: uu____17357
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17418 =
                             let uu____17425 =
                               let uu____17432 = thunk_ens ens  in
                               [uu____17432; nil_pat; dec]  in
                             req_true :: uu____17425  in
                           unit_tm :: uu____17418
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17492 =
                             let uu____17499 =
                               let uu____17506 = thunk_ens ens  in
                               [uu____17506; smtpat; dec]  in
                             req_true :: uu____17499  in
                           unit_tm :: uu____17492
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17566 =
                             let uu____17573 =
                               let uu____17580 = thunk_ens ens  in
                               [uu____17580; nil_pat; dec]  in
                             req :: uu____17573  in
                           unit_tm :: uu____17566
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17640 =
                             let uu____17647 =
                               let uu____17654 = thunk_ens ens  in
                               [uu____17654; smtpat]  in
                             req :: uu____17647  in
                           unit_tm :: uu____17640
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17719 =
                             let uu____17726 =
                               let uu____17733 = thunk_ens ens  in
                               [uu____17733; dec; smtpat]  in
                             req :: uu____17726  in
                           unit_tm :: uu____17719
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17795 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17795, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17823 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17823
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17825 =
                          let uu____17827 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17827  in
                        uu____17825 = "Tot")
                     ->
                     let uu____17830 =
                       let uu____17837 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17837, [])  in
                     (uu____17830, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17855 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17855
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17857 =
                          let uu____17859 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17859  in
                        uu____17857 = "GTot")
                     ->
                     let uu____17862 =
                       let uu____17869 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17869, [])  in
                     (uu____17862, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17887 =
                         let uu____17889 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17889  in
                       uu____17887 = "Type") ||
                        (let uu____17893 =
                           let uu____17895 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17895  in
                         uu____17893 = "Type0"))
                       ||
                       (let uu____17899 =
                          let uu____17901 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17901  in
                        uu____17899 = "Effect")
                     ->
                     let uu____17904 =
                       let uu____17911 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17911, [])  in
                     (uu____17904, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17934 when allow_type_promotion ->
                     let default_effect =
                       let uu____17936 = FStar_Options.ml_ish ()  in
                       if uu____17936
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17942 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17942
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17949 =
                       let uu____17956 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17956, [])  in
                     (uu____17949, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17979 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17998 = pre_process_comp_typ t  in
          match uu____17998 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18050 =
                    let uu____18056 =
                      let uu____18058 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18058
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18056)
                     in
                  fail uu____18050)
               else ();
               (let is_universe uu____18074 =
                  match uu____18074 with
                  | (uu____18080,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18082 = FStar_Util.take is_universe args  in
                match uu____18082 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18141  ->
                           match uu____18141 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18148 =
                      let uu____18163 = FStar_List.hd args1  in
                      let uu____18172 = FStar_List.tl args1  in
                      (uu____18163, uu____18172)  in
                    (match uu____18148 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18227 =
                           let is_decrease uu____18266 =
                             match uu____18266 with
                             | (t1,uu____18277) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18288;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18289;_},uu____18290::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18329 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18227 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18446  ->
                                        match uu____18446 with
                                        | (t1,uu____18456) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18465,(arg,uu____18467)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18506 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18527 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18539 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18539
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18546 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18546
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18556 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18556
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18563 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18563
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18570 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18570
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18577 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18577
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18598 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18598
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
                                                    let uu____18689 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18689
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
                                              | uu____18710 -> pat  in
                                            let uu____18711 =
                                              let uu____18722 =
                                                let uu____18733 =
                                                  let uu____18742 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18742, aq)  in
                                                [uu____18733]  in
                                              ens :: uu____18722  in
                                            req :: uu____18711
                                        | uu____18783 -> rest2
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
        let uu___2414_18818 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2414_18818.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2414_18818.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2421_18872 = b  in
             {
               FStar_Parser_AST.b = (uu___2421_18872.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2421_18872.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2421_18872.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18901 body1 =
          match uu____18901 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18947::uu____18948) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18966 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2440_18994 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18995 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2440_18994.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18995;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2440_18994.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19058 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19058))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19089 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19089 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2453_19099 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2453_19099.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2453_19099.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19105 =
                     let uu____19108 =
                       let uu____19109 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19109]  in
                     no_annot_abs uu____19108 body2  in
                   FStar_All.pipe_left setpos uu____19105  in
                 let uu____19130 =
                   let uu____19131 =
                     let uu____19148 =
                       let uu____19151 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19151
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19153 =
                       let uu____19164 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19164]  in
                     (uu____19148, uu____19153)  in
                   FStar_Syntax_Syntax.Tm_app uu____19131  in
                 FStar_All.pipe_left mk uu____19130)
        | uu____19203 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19268 = q (rest, pats, body)  in
              let uu____19271 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19268 uu____19271
                FStar_Parser_AST.Formula
               in
            let uu____19272 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19272 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19283 -> failwith "impossible"  in
      let uu____19287 =
        let uu____19288 = unparen f  in uu____19288.FStar_Parser_AST.tm  in
      match uu____19287 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19301,uu____19302) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19326,uu____19327) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19383 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19383
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19427 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19427
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19491 -> desugar_term env f

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
          let uu____19502 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19502)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19507 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19507)
      | FStar_Parser_AST.TVariable x ->
          let uu____19511 =
            let uu____19512 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19512
             in
          ((FStar_Pervasives_Native.Some x), uu____19511)
      | FStar_Parser_AST.NoName t ->
          let uu____19516 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19516)
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
      fun uu___11_19524  ->
        match uu___11_19524 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19546 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19546, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19563 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19563 with
             | (env1,a1) ->
                 let uu____19580 =
                   let uu____19587 = trans_aqual env1 imp  in
                   ((let uu___2553_19593 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2553_19593.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2553_19593.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19587)
                    in
                 (uu____19580, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19601  ->
      match uu___12_19601 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19605 =
            let uu____19606 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19606  in
          FStar_Pervasives_Native.Some uu____19605
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19634 =
        FStar_List.fold_left
          (fun uu____19667  ->
             fun b  ->
               match uu____19667 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2571_19711 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2571_19711.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2571_19711.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2571_19711.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19726 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19726 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2581_19744 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2581_19744.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2581_19744.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19745 =
                               let uu____19752 =
                                 let uu____19757 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19757)  in
                               uu____19752 :: out  in
                             (env2, uu____19745))
                    | uu____19768 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19634 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19856 =
          let uu____19857 = unparen t  in uu____19857.FStar_Parser_AST.tm  in
        match uu____19856 with
        | FStar_Parser_AST.Var lid when
            let uu____19859 = FStar_Ident.string_of_lid lid  in
            uu____19859 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19863 ->
            let uu____19864 =
              let uu____19870 =
                let uu____19872 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19872  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19870)  in
            FStar_Errors.raise_error uu____19864 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19889) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19891) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19894 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19912 = binder_ident b  in
         FStar_Common.list_of_option uu____19912) bs
  
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
               (fun uu___13_19949  ->
                  match uu___13_19949 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19954 -> false))
           in
        let quals2 q =
          let uu____19968 =
            (let uu____19972 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19972) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19968
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19989 = FStar_Ident.range_of_lid disc_name  in
                let uu____19990 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19989;
                  FStar_Syntax_Syntax.sigquals = uu____19990;
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
            let uu____20030 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20066  ->
                        match uu____20066 with
                        | (x,uu____20077) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20087 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20087)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20089 =
                                   let uu____20091 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20091  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20089)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20109 =
                                  FStar_List.filter
                                    (fun uu___14_20113  ->
                                       match uu___14_20113 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20116 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20109
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20131  ->
                                        match uu___15_20131 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20136 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20139 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20139;
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
                                 let uu____20146 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20146
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20157 =
                                   let uu____20162 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20162  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20157;
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
                                 let uu____20166 =
                                   let uu____20167 =
                                     let uu____20174 =
                                       let uu____20177 =
                                         let uu____20178 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20178
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20177]  in
                                     ((false, [lb]), uu____20174)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20167
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20166;
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
            FStar_All.pipe_right uu____20030 FStar_List.flatten
  
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
            (lid,uu____20227,t,uu____20229,n,uu____20231) when
            let uu____20238 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20238 ->
            let uu____20240 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20240 with
             | (formals,uu____20250) ->
                 (match formals with
                  | [] -> []
                  | uu____20263 ->
                      let filter_records uu___16_20271 =
                        match uu___16_20271 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20274,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20286 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20288 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20288 with
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
                      let uu____20300 = FStar_Util.first_N n formals  in
                      (match uu____20300 with
                       | (uu____20329,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20363 -> []
  
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
                        let uu____20457 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20457
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20481 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20481
                        then
                          let uu____20487 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20487
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20491 =
                          let uu____20496 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20496  in
                        let uu____20497 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20503 =
                              let uu____20506 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20506  in
                            FStar_Syntax_Util.arrow typars uu____20503
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20511 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20491;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20497;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20511;
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
          let tycon_id uu___17_20565 =
            match uu___17_20565 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20567,uu____20568) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20578,uu____20579,uu____20580) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20590,uu____20591,uu____20592) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20614,uu____20615,uu____20616) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20654) ->
                let uu____20655 =
                  let uu____20656 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20656  in
                let uu____20657 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20655 uu____20657
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20659 =
                  let uu____20660 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20660  in
                let uu____20661 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20659 uu____20661
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20663) ->
                let uu____20664 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20664 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20666 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20666 FStar_Parser_AST.Type_level
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
              | uu____20696 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20704 =
                     let uu____20705 =
                       let uu____20712 = binder_to_term b  in
                       (out, uu____20712, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20705  in
                   FStar_Parser_AST.mk_term uu____20704
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20724 =
            match uu___18_20724 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20756 =
                    let uu____20762 =
                      let uu____20764 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20764  in
                    let uu____20767 = FStar_Ident.range_of_id id  in
                    (uu____20762, uu____20767)  in
                  FStar_Ident.mk_ident uu____20756  in
                let mfields =
                  FStar_List.map
                    (fun uu____20780  ->
                       match uu____20780 with
                       | (x,t) ->
                           let uu____20787 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20787
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20789 =
                    let uu____20790 =
                      let uu____20791 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20791  in
                    let uu____20792 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20790 uu____20792
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20789 parms  in
                let constrTyp =
                  let uu____20794 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20794 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20800 = binder_idents parms  in id :: uu____20800
                   in
                (FStar_List.iter
                   (fun uu____20814  ->
                      match uu____20814 with
                      | (f,uu____20820) ->
                          let uu____20821 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20821
                          then
                            let uu____20826 =
                              let uu____20832 =
                                let uu____20834 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20834
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20832)
                               in
                            let uu____20838 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20826 uu____20838
                          else ()) fields;
                 (let uu____20841 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20841)))
            | uu____20895 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20935 =
            match uu___19_20935 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20959 = typars_of_binders _env binders  in
                (match uu____20959 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20995 =
                         let uu____20996 =
                           let uu____20997 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20997  in
                         let uu____20998 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20996 uu____20998
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20995 binders  in
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
                     let uu____21007 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____21007 with
                      | (_env1,uu____21024) ->
                          let uu____21031 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21031 with
                           | (_env2,uu____21048) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21055 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21098 =
              FStar_List.fold_left
                (fun uu____21132  ->
                   fun uu____21133  ->
                     match (uu____21132, uu____21133) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21202 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21202 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21098 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21293 =
                      let uu____21294 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21294  in
                    FStar_Pervasives_Native.Some uu____21293
                | uu____21295 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21303 = desugar_abstract_tc quals env [] tc  in
              (match uu____21303 with
               | (uu____21316,uu____21317,se,uu____21319) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21322,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21341 =
                                 let uu____21343 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21343  in
                               if uu____21341
                               then
                                 let uu____21346 =
                                   let uu____21352 =
                                     let uu____21354 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21354
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21352)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21346
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
                           | uu____21367 ->
                               let uu____21368 =
                                 let uu____21375 =
                                   let uu____21376 =
                                     let uu____21391 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21391)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21376
                                    in
                                 FStar_Syntax_Syntax.mk uu____21375  in
                               uu____21368 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2858_21404 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2858_21404.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2858_21404.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2858_21404.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2858_21404.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21405 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21420 = typars_of_binders env binders  in
              (match uu____21420 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21454 =
                           FStar_Util.for_some
                             (fun uu___20_21457  ->
                                match uu___20_21457 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21460 -> false) quals
                            in
                         if uu____21454
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21468 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21468
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21473 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21479  ->
                               match uu___21_21479 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21482 -> false))
                        in
                     if uu____21473
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21496 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21496
                     then
                       let uu____21502 =
                         let uu____21509 =
                           let uu____21510 = unparen t  in
                           uu____21510.FStar_Parser_AST.tm  in
                         match uu____21509 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21531 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21561)::args_rev ->
                                   let uu____21573 =
                                     let uu____21574 = unparen last_arg  in
                                     uu____21574.FStar_Parser_AST.tm  in
                                   (match uu____21573 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21602 -> ([], args))
                               | uu____21611 -> ([], args)  in
                             (match uu____21531 with
                              | (cattributes,args1) ->
                                  let uu____21650 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21650))
                         | uu____21661 -> (t, [])  in
                       match uu____21502 with
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
                                  (fun uu___22_21684  ->
                                     match uu___22_21684 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21687 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21695)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21715 = tycon_record_as_variant trec  in
              (match uu____21715 with
               | (t,fs) ->
                   let uu____21732 =
                     let uu____21735 =
                       let uu____21736 =
                         let uu____21745 =
                           let uu____21748 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21748  in
                         (uu____21745, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21736  in
                     uu____21735 :: quals  in
                   desugar_tycon env d uu____21732 [t])
          | uu____21753::uu____21754 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21912 = et  in
                match uu____21912 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22122 ->
                         let trec = tc  in
                         let uu____22142 = tycon_record_as_variant trec  in
                         (match uu____22142 with
                          | (t,fs) ->
                              let uu____22198 =
                                let uu____22201 =
                                  let uu____22202 =
                                    let uu____22211 =
                                      let uu____22214 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22214  in
                                    (uu____22211, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22202
                                   in
                                uu____22201 :: quals1  in
                              collect_tcs uu____22198 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22292 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22292 with
                          | (env2,uu____22349,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22486 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22486 with
                          | (env2,uu____22543,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22659 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22705 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22705 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23157  ->
                             match uu___24_23157 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23211,uu____23212);
                                    FStar_Syntax_Syntax.sigrng = uu____23213;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23214;
                                    FStar_Syntax_Syntax.sigmeta = uu____23215;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23216;
                                    FStar_Syntax_Syntax.sigopts = uu____23217;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23279 =
                                     typars_of_binders env1 binders  in
                                   match uu____23279 with
                                   | (env2,tpars1) ->
                                       let uu____23306 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23306 with
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
                                 let uu____23335 =
                                   let uu____23346 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23346)  in
                                 [uu____23335]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23382);
                                    FStar_Syntax_Syntax.sigrng = uu____23383;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23385;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23386;
                                    FStar_Syntax_Syntax.sigopts = uu____23387;_},constrs,tconstr,quals1)
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
                                 let uu____23478 = push_tparams env1 tpars
                                    in
                                 (match uu____23478 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23537  ->
                                             match uu____23537 with
                                             | (x,uu____23549) ->
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
                                        let uu____23560 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23560
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23583 =
                                        let uu____23602 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23679  ->
                                                  match uu____23679 with
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
                                                        let uu____23722 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23722
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
                                                                uu___23_23733
                                                                 ->
                                                                match uu___23_23733
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23745
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23753 =
                                                        let uu____23764 =
                                                          let uu____23765 =
                                                            let uu____23766 =
                                                              let uu____23782
                                                                =
                                                                let uu____23783
                                                                  =
                                                                  let uu____23786
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23786
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23783
                                                                 in
                                                              (name, univs,
                                                                uu____23782,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23766
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23765;
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
                                                        (tps, uu____23764)
                                                         in
                                                      (name, uu____23753)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23602
                                         in
                                      (match uu____23583 with
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
                             | uu____23918 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23999  ->
                             match uu____23999 with | (uu____24010,se) -> se))
                      in
                   let uu____24024 =
                     let uu____24031 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24031 rng
                      in
                   (match uu____24024 with
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
                               (fun uu____24076  ->
                                  match uu____24076 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24124,tps,k,uu____24127,constrs)
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
                                      let uu____24148 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24163 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24180,uu____24181,uu____24182,uu____24183,uu____24184)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24191
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24163
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24195 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24202  ->
                                                          match uu___25_24202
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24204 ->
                                                              true
                                                          | uu____24214 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24195))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24148
                                  | uu____24216 -> []))
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
      let uu____24253 =
        FStar_List.fold_left
          (fun uu____24288  ->
             fun b  ->
               match uu____24288 with
               | (env1,binders1) ->
                   let uu____24332 = desugar_binder env1 b  in
                   (match uu____24332 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24355 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24355 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24408 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24253 with
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
          let uu____24512 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24519  ->
                    match uu___26_24519 with
                    | FStar_Syntax_Syntax.Reflectable uu____24521 -> true
                    | uu____24523 -> false))
             in
          if uu____24512
          then
            let monad_env =
              let uu____24527 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24527  in
            let reflect_lid =
              let uu____24529 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24529
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
        let warn1 uu____24580 =
          if warn
          then
            let uu____24582 =
              let uu____24588 =
                let uu____24590 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24590
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24588)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24582
          else ()  in
        let uu____24596 = FStar_Syntax_Util.head_and_args at  in
        match uu____24596 with
        | (hd,args) ->
            let uu____24649 =
              let uu____24650 = FStar_Syntax_Subst.compress hd  in
              uu____24650.FStar_Syntax_Syntax.n  in
            (match uu____24649 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24694)::[] ->
                      let uu____24719 =
                        let uu____24724 =
                          let uu____24733 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24733 a1  in
                        uu____24724 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24719 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24756 =
                             let uu____24762 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24762  in
                           (uu____24756, true)
                       | uu____24777 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24793 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24815 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24932 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24932 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24981 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24981 with | (res1,uu____25003) -> rebind res1 true)
  
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
        | uu____25330 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25388 = get_fail_attr1 warn at  in
             comb uu____25388 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25423 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25423 with
        | FStar_Pervasives_Native.None  ->
            let uu____25426 =
              let uu____25432 =
                let uu____25434 =
                  let uu____25436 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25436 " not found"  in
                Prims.op_Hat "Effect name " uu____25434  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25432)  in
            FStar_Errors.raise_error uu____25426 r
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
                    let uu____25592 = desugar_binders monad_env eff_binders
                       in
                    match uu____25592 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25631 =
                            let uu____25640 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25640  in
                          FStar_List.length uu____25631  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25658 =
                              let uu____25664 =
                                let uu____25666 =
                                  let uu____25668 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25668
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25666  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25664)
                               in
                            FStar_Errors.raise_error uu____25658
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
                                (uu____25736,uu____25737,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25739,uu____25740,uu____25741))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25756 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25759 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25771 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25771 mandatory_members)
                              eff_decls
                             in
                          match uu____25759 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25790 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25819  ->
                                        fun decl  ->
                                          match uu____25819 with
                                          | (env2,out) ->
                                              let uu____25839 =
                                                desugar_decl env2 decl  in
                                              (match uu____25839 with
                                               | (env3,ses) ->
                                                   let uu____25852 =
                                                     let uu____25855 =
                                                       FStar_List.hd ses  in
                                                     uu____25855 :: out  in
                                                   (env3, uu____25852)))
                                     (env1, []))
                                 in
                              (match uu____25790 with
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
                                                 (uu____25901,uu____25902,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25905,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25906,(def,uu____25908)::
                                                        (cps_type,uu____25910)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25911;
                                                     FStar_Parser_AST.level =
                                                       uu____25912;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25945 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25945 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25977 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25978 =
                                                        let uu____25979 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25979
                                                         in
                                                      let uu____25986 =
                                                        let uu____25987 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25987
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25977;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25978;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25986
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25994,uu____25995,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25998,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26014 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26014 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26046 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26047 =
                                                        let uu____26048 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26048
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26046;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26047;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26055 ->
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
                                       let uu____26074 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26074
                                        in
                                     let uu____26076 =
                                       let uu____26077 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26077
                                        in
                                     ([], uu____26076)  in
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
                                       let uu____26099 =
                                         let uu____26100 =
                                           let uu____26103 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26103
                                            in
                                         let uu____26105 =
                                           let uu____26108 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26108
                                            in
                                         let uu____26110 =
                                           let uu____26113 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26113
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
                                             uu____26100;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26105;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26110
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26099
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26147 =
                                            match uu____26147 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26194 =
                                            let uu____26195 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26197 =
                                              let uu____26202 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26202 to_comb
                                               in
                                            let uu____26220 =
                                              let uu____26225 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26225 to_comb
                                               in
                                            let uu____26243 =
                                              let uu____26248 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26248 to_comb
                                               in
                                            let uu____26266 =
                                              let uu____26271 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26271 to_comb
                                               in
                                            let uu____26289 =
                                              let uu____26294 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26294 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26195;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26197;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26220;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26243;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26266;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26289
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26194)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26317  ->
                                                 match uu___27_26317 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26320 -> true
                                                 | uu____26322 -> false)
                                              qualifiers
                                             in
                                          let uu____26324 =
                                            let uu____26325 =
                                              lookup "return_wp"  in
                                            let uu____26327 =
                                              lookup "bind_wp"  in
                                            let uu____26329 =
                                              lookup "stronger"  in
                                            let uu____26331 =
                                              lookup "if_then_else"  in
                                            let uu____26333 = lookup "ite_wp"
                                               in
                                            let uu____26335 =
                                              lookup "close_wp"  in
                                            let uu____26337 =
                                              lookup "trivial"  in
                                            let uu____26339 =
                                              if rr
                                              then
                                                let uu____26345 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26345
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26349 =
                                              if rr
                                              then
                                                let uu____26355 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26355
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26359 =
                                              if rr
                                              then
                                                let uu____26365 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26365
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26325;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26327;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26329;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26331;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26333;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26335;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26337;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26339;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26349;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26359
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26324)
                                      in
                                   let sigel =
                                     let uu____26370 =
                                       let uu____26371 =
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
                                           uu____26371
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26370
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
                                               let uu____26388 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26388) env3)
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
                let uu____26411 = desugar_binders env1 eff_binders  in
                match uu____26411 with
                | (env2,binders) ->
                    let uu____26448 =
                      let uu____26459 = head_and_args defn  in
                      match uu____26459 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26496 ->
                                let uu____26497 =
                                  let uu____26503 =
                                    let uu____26505 =
                                      let uu____26507 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26507 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26505  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26503)
                                   in
                                FStar_Errors.raise_error uu____26497
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26513 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26543)::args_rev ->
                                let uu____26555 =
                                  let uu____26556 = unparen last_arg  in
                                  uu____26556.FStar_Parser_AST.tm  in
                                (match uu____26555 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26584 -> ([], args))
                            | uu____26593 -> ([], args)  in
                          (match uu____26513 with
                           | (cattributes,args1) ->
                               let uu____26636 = desugar_args env2 args1  in
                               let uu____26637 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26636, uu____26637))
                       in
                    (match uu____26448 with
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
                          (let uu____26677 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26677 with
                           | (ed_binders,uu____26691,ed_binders_opening) ->
                               let sub' shift_n uu____26710 =
                                 match uu____26710 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26725 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26725 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26729 =
                                       let uu____26730 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26730)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26729
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26751 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26752 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26753 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26769 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26770 =
                                          let uu____26771 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26771
                                           in
                                        let uu____26786 =
                                          let uu____26787 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26787
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26769;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26770;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26786
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
                                     uu____26751;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26752;
                                   FStar_Syntax_Syntax.actions = uu____26753;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26803 =
                                   let uu____26806 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26806 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26803;
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
                                           let uu____26821 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26821) env3)
                                  in
                               let env5 =
                                 let uu____26823 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26823
                                 then
                                   let reflect_lid =
                                     let uu____26830 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26830
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
             let uu____26863 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26863) ats
         in
      let env0 =
        let uu____26884 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26884 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26899 =
        let uu____26906 = get_fail_attr false attrs  in
        match uu____26906 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3413_26943 = d  in
              {
                FStar_Parser_AST.d = (uu___3413_26943.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3413_26943.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3413_26943.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26944 =
              FStar_Errors.catch_errors
                (fun uu____26962  ->
                   FStar_Options.with_saved_options
                     (fun uu____26968  -> desugar_decl_noattrs env d1))
               in
            (match uu____26944 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3428_27028 = se  in
                             let uu____27029 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3428_27028.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3428_27028.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3428_27028.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3428_27028.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27029;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3428_27028.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____27082 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27082 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27131 =
                                 let uu____27137 =
                                   let uu____27139 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27142 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27145 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27147 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27149 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27139 uu____27142 uu____27145
                                     uu____27147 uu____27149
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27137)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27131);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26899 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27187;
                FStar_Syntax_Syntax.sigrng = uu____27188;
                FStar_Syntax_Syntax.sigquals = uu____27189;
                FStar_Syntax_Syntax.sigmeta = uu____27190;
                FStar_Syntax_Syntax.sigattrs = uu____27191;
                FStar_Syntax_Syntax.sigopts = uu____27192;_}::[] ->
                let uu____27205 =
                  let uu____27208 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27208  in
                FStar_All.pipe_right uu____27205
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27216 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27216))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27229;
                FStar_Syntax_Syntax.sigrng = uu____27230;
                FStar_Syntax_Syntax.sigquals = uu____27231;
                FStar_Syntax_Syntax.sigmeta = uu____27232;
                FStar_Syntax_Syntax.sigattrs = uu____27233;
                FStar_Syntax_Syntax.sigopts = uu____27234;_}::uu____27235 ->
                let uu____27260 =
                  let uu____27263 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27263  in
                FStar_All.pipe_right uu____27260
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27271 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27271))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27287;
                FStar_Syntax_Syntax.sigquals = uu____27288;
                FStar_Syntax_Syntax.sigmeta = uu____27289;
                FStar_Syntax_Syntax.sigattrs = uu____27290;
                FStar_Syntax_Syntax.sigopts = uu____27291;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27312 -> []  in
          let attrs1 =
            let uu____27318 = val_attrs sigelts  in
            FStar_List.append attrs uu____27318  in
          let uu____27321 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3488_27325 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3488_27325.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3488_27325.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3488_27325.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3488_27325.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3488_27325.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27321)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27332 = desugar_decl_aux env d  in
      match uu____27332 with
      | (env1,ses) ->
          let uu____27343 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27343)

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
          let uu____27375 = FStar_Syntax_DsEnv.iface env  in
          if uu____27375
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27390 =
               let uu____27392 =
                 let uu____27394 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27395 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27394
                   uu____27395
                  in
               Prims.op_Negation uu____27392  in
             if uu____27390
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27409 =
                  let uu____27411 =
                    let uu____27413 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27413 lid  in
                  Prims.op_Negation uu____27411  in
                if uu____27409
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27427 =
                     let uu____27429 =
                       let uu____27431 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27431
                         lid
                        in
                     Prims.op_Negation uu____27429  in
                   if uu____27427
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27449 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27449, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27478)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27497 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27506 =
            let uu____27511 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27511 tcs  in
          (match uu____27506 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27528 =
                   let uu____27529 =
                     let uu____27536 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27536  in
                   [uu____27529]  in
                 let uu____27549 =
                   let uu____27552 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27555 =
                     let uu____27566 =
                       let uu____27575 =
                         let uu____27576 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27576  in
                       FStar_Syntax_Syntax.as_arg uu____27575  in
                     [uu____27566]  in
                   FStar_Syntax_Util.mk_app uu____27552 uu____27555  in
                 FStar_Syntax_Util.abs uu____27528 uu____27549
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27616,id))::uu____27618 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27621::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27625 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27625 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27631 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27631]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27652) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27662,uu____27663,uu____27664,uu____27665,uu____27666)
                     ->
                     let uu____27675 =
                       let uu____27676 =
                         let uu____27677 =
                           let uu____27684 = mkclass lid  in
                           (meths, uu____27684)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27677  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27676;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27675]
                 | uu____27687 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27721;
                    FStar_Parser_AST.prange = uu____27722;_},uu____27723)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27733;
                    FStar_Parser_AST.prange = uu____27734;_},uu____27735)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27751;
                         FStar_Parser_AST.prange = uu____27752;_},uu____27753);
                    FStar_Parser_AST.prange = uu____27754;_},uu____27755)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27777;
                         FStar_Parser_AST.prange = uu____27778;_},uu____27779);
                    FStar_Parser_AST.prange = uu____27780;_},uu____27781)::[]
                   -> false
               | (p,uu____27810)::[] ->
                   let uu____27819 = is_app_pattern p  in
                   Prims.op_Negation uu____27819
               | uu____27821 -> false)
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
            let uu____27896 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27896 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27909 =
                     let uu____27910 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27910.FStar_Syntax_Syntax.n  in
                   match uu____27909 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27920) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27951 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27976  ->
                                match uu____27976 with
                                | (qs,ats) ->
                                    let uu____28003 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____28003 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27951 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28057::uu____28058 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28061 -> val_quals  in
                            let quals2 =
                              let uu____28065 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28098  ->
                                        match uu____28098 with
                                        | (uu____28112,(uu____28113,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28065
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28133 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28133
                              then
                                let uu____28139 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3665_28154 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3667_28156 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3667_28156.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3667_28156.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3665_28154.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28139)
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
                   | uu____28181 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28189 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28208 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28189 with
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
                       let uu___3690_28245 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3690_28245.FStar_Parser_AST.prange)
                       }
                   | uu____28252 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3694_28259 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3694_28259.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3694_28259.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28275 =
                     let uu____28276 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28276  in
                   FStar_Parser_AST.mk_term uu____28275
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28300 id_opt =
                   match uu____28300 with
                   | (env1,ses) ->
                       let uu____28322 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28334 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28334
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28336 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28336
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
                               let uu____28342 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28342
                                in
                             let bv_pat1 =
                               let uu____28346 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28346
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28322 with
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
                            let uu____28407 = desugar_decl env1 id_decl  in
                            (match uu____28407 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28443 id =
                   match uu____28443 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28482 =
                   match uu____28482 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28506 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28506 FStar_Util.set_elements
                    in
                 let uu____28513 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28516 = is_var_pattern pat  in
                      Prims.op_Negation uu____28516)
                    in
                 if uu____28513
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
            let uu____28540 = close_fun env t  in
            desugar_term env uu____28540  in
          let quals1 =
            let uu____28544 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28544
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28556 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28556;
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
                let uu____28569 =
                  let uu____28578 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28578]  in
                let uu____28597 =
                  let uu____28600 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28600
                   in
                FStar_Syntax_Util.arrow uu____28569 uu____28597
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
          uu____28663) ->
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
          let uu____28680 =
            let uu____28682 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28682  in
          if uu____28680
          then
            let uu____28689 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28707 =
                    let uu____28710 =
                      let uu____28711 = desugar_term env t  in
                      ([], uu____28711)  in
                    FStar_Pervasives_Native.Some uu____28710  in
                  (uu____28707, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28724 =
                    let uu____28727 =
                      let uu____28728 = desugar_term env wp  in
                      ([], uu____28728)  in
                    FStar_Pervasives_Native.Some uu____28727  in
                  let uu____28735 =
                    let uu____28738 =
                      let uu____28739 = desugar_term env t  in
                      ([], uu____28739)  in
                    FStar_Pervasives_Native.Some uu____28738  in
                  (uu____28724, uu____28735)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28751 =
                    let uu____28754 =
                      let uu____28755 = desugar_term env t  in
                      ([], uu____28755)  in
                    FStar_Pervasives_Native.Some uu____28754  in
                  (FStar_Pervasives_Native.None, uu____28751)
               in
            (match uu____28689 with
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
                   let uu____28789 =
                     let uu____28792 =
                       let uu____28793 = desugar_term env t  in
                       ([], uu____28793)  in
                     FStar_Pervasives_Native.Some uu____28792  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28789
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
             | uu____28800 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28813 =
            let uu____28814 =
              let uu____28815 =
                let uu____28816 =
                  let uu____28827 =
                    let uu____28828 = desugar_term env bind  in
                    ([], uu____28828)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28827,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28816  in
              {
                FStar_Syntax_Syntax.sigel = uu____28815;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28814]  in
          (env, uu____28813)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28847 =
              let uu____28848 =
                let uu____28855 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28855, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28848  in
            {
              FStar_Syntax_Syntax.sigel = uu____28847;
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
      let uu____28882 =
        FStar_List.fold_left
          (fun uu____28902  ->
             fun d  ->
               match uu____28902 with
               | (env1,sigelts) ->
                   let uu____28922 = desugar_decl env1 d  in
                   (match uu____28922 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28882 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29013) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29017;
               FStar_Syntax_Syntax.exports = uu____29018;
               FStar_Syntax_Syntax.is_interface = uu____29019;_},FStar_Parser_AST.Module
             (current_lid,uu____29021)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29030) ->
              let uu____29033 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29033
           in
        let uu____29038 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29080 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29080, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29102 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29102, mname, decls, false)
           in
        match uu____29038 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29144 = desugar_decls env2 decls  in
            (match uu____29144 with
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
          let uu____29212 =
            (FStar_Options.interactive ()) &&
              (let uu____29215 =
                 let uu____29217 =
                   let uu____29219 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29219  in
                 FStar_Util.get_file_extension uu____29217  in
               FStar_List.mem uu____29215 ["fsti"; "fsi"])
             in
          if uu____29212 then as_interface m else m  in
        let uu____29233 = desugar_modul_common curmod env m1  in
        match uu____29233 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29255 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29255, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29277 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29277 with
      | (env1,modul,pop_when_done) ->
          let uu____29294 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29294 with
           | (env2,modul1) ->
               ((let uu____29306 =
                   let uu____29308 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29308  in
                 if uu____29306
                 then
                   let uu____29311 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29311
                 else ());
                (let uu____29316 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29316, modul1))))
  
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
        (fun uu____29366  ->
           let uu____29367 = desugar_modul env modul  in
           match uu____29367 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29405  ->
           let uu____29406 = desugar_decls env decls  in
           match uu____29406 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29457  ->
             let uu____29458 = desugar_partial_modul modul env a_modul  in
             match uu____29458 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29553 ->
                  let t =
                    let uu____29563 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29563  in
                  let uu____29576 =
                    let uu____29577 = FStar_Syntax_Subst.compress t  in
                    uu____29577.FStar_Syntax_Syntax.n  in
                  (match uu____29576 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29589,uu____29590)
                       -> bs1
                   | uu____29615 -> failwith "Impossible")
               in
            let uu____29625 =
              let uu____29632 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29632
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29625 with
            | (binders,uu____29634,binders_opening) ->
                let erase_term t =
                  let uu____29642 =
                    let uu____29643 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29643  in
                  FStar_Syntax_Subst.close binders uu____29642  in
                let erase_tscheme uu____29661 =
                  match uu____29661 with
                  | (us,t) ->
                      let t1 =
                        let uu____29681 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29681 t  in
                      let uu____29684 =
                        let uu____29685 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29685  in
                      ([], uu____29684)
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
                    | uu____29708 ->
                        let bs =
                          let uu____29718 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29718  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29758 =
                          let uu____29759 =
                            let uu____29762 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29762  in
                          uu____29759.FStar_Syntax_Syntax.n  in
                        (match uu____29758 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29764,uu____29765) -> bs1
                         | uu____29790 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29798 =
                      let uu____29799 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29799  in
                    FStar_Syntax_Subst.close binders uu____29798  in
                  let uu___3990_29800 = action  in
                  let uu____29801 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29802 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3990_29800.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3990_29800.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29801;
                    FStar_Syntax_Syntax.action_typ = uu____29802
                  }  in
                let uu___3992_29803 = ed  in
                let uu____29804 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29805 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29806 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29807 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3992_29803.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3992_29803.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29804;
                  FStar_Syntax_Syntax.signature = uu____29805;
                  FStar_Syntax_Syntax.combinators = uu____29806;
                  FStar_Syntax_Syntax.actions = uu____29807;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3992_29803.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3999_29823 = se  in
                  let uu____29824 =
                    let uu____29825 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29825  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29824;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3999_29823.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3999_29823.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3999_29823.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3999_29823.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3999_29823.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29827 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29828 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29828 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29845 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29845
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29847 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29847)
  