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
  
let (unit_ty : FStar_Range.range -> FStar_Parser_AST.term) =
  fun rng  ->
    FStar_Parser_AST.mk_term
      (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid) rng
      FStar_Parser_AST.Type_level
  
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
                            FStar_Syntax_Syntax.pos = uu____556;
                            FStar_Syntax_Syntax.vars = uu____557;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____585 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____585 " is deprecated"  in
                         let msg1 =
                           if (FStar_List.length args) > Prims.int_zero
                           then
                             let uu____601 =
                               let uu____602 =
                                 let uu____605 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____605  in
                               uu____602.FStar_Syntax_Syntax.n  in
                             match uu____601 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____628))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____635 -> msg
                           else msg  in
                         let uu____638 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____638
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____643 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____643 " is deprecated"  in
                         let uu____646 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____646
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____648 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'uuuuuu664 .
    'uuuuuu664 ->
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
        let uu____717 =
          let uu____718 =
            let uu____719 =
              let uu____725 = FStar_Parser_AST.compile_op n s r  in
              (uu____725, r)  in
            FStar_Ident.mk_ident uu____719  in
          [uu____718]  in
        FStar_All.pipe_right uu____717 FStar_Ident.lid_of_ids
  
let (op_as_term :
  env_t ->
    Prims.int ->
      FStar_Ident.ident ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun arity  ->
      fun op  ->
        let r l dd =
          let uu____763 =
            let uu____764 =
              let uu____765 =
                let uu____766 = FStar_Ident.range_of_id op  in
                FStar_Ident.set_lid_range l uu____766  in
              FStar_Syntax_Syntax.lid_as_fv uu____765 dd
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____764 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_Pervasives_Native.Some uu____763  in
        let fallback uu____774 =
          let uu____775 = FStar_Ident.text_of_id op  in
          match uu____775 with
          | "=" ->
              r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.delta_equational
          | ":=" ->
              r FStar_Parser_Const.write_lid
                FStar_Syntax_Syntax.delta_equational
          | "<" ->
              r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.delta_equational
          | "<=" ->
              r FStar_Parser_Const.op_LTE
                FStar_Syntax_Syntax.delta_equational
          | ">" ->
              r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.delta_equational
          | ">=" ->
              r FStar_Parser_Const.op_GTE
                FStar_Syntax_Syntax.delta_equational
          | "&&" ->
              r FStar_Parser_Const.op_And
                FStar_Syntax_Syntax.delta_equational
          | "||" ->
              r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.delta_equational
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
              let uu____796 = FStar_Options.ml_ish ()  in
              if uu____796
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
          | uu____821 -> FStar_Pervasives_Native.None  in
        let uu____823 =
          let uu____826 =
            let uu____827 = FStar_Ident.text_of_id op  in
            let uu____829 = FStar_Ident.range_of_id op  in
            compile_op_lid arity uu____827 uu____829  in
          desugar_name'
            (fun t  ->
               let uu___202_837 = t  in
               let uu____838 = FStar_Ident.range_of_id op  in
               {
                 FStar_Syntax_Syntax.n = (uu___202_837.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____838;
                 FStar_Syntax_Syntax.vars =
                   (uu___202_837.FStar_Syntax_Syntax.vars)
               }) env true uu____826
           in
        match uu____823 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____843 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____858 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____867 = FStar_Ident.text_of_id x  in
             let uu____869 = FStar_Ident.text_of_id y  in
             uu____867 = uu____869) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____882 = FStar_Ident.text_of_id x  in
              let uu____884 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____882 uu____884)) uu____858
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____919 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____923 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____923 with | (env1,uu____935) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____938,term) ->
          let uu____940 = free_type_vars env term  in (env, uu____940)
      | FStar_Parser_AST.TAnnotated (id,uu____946) ->
          let uu____947 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____947 with | (env1,uu____959) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____963 = free_type_vars env t  in (env, uu____963)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____970 =
        let uu____971 = unparen t  in uu____971.FStar_Parser_AST.tm  in
      match uu____970 with
      | FStar_Parser_AST.Labeled uu____974 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____987 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____987 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____992 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____995 -> []
      | FStar_Parser_AST.Uvar uu____996 -> []
      | FStar_Parser_AST.Var uu____997 -> []
      | FStar_Parser_AST.Projector uu____998 -> []
      | FStar_Parser_AST.Discrim uu____1003 -> []
      | FStar_Parser_AST.Name uu____1004 -> []
      | FStar_Parser_AST.Requires (t1,uu____1006) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1014) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1021,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1040,ts) ->
          FStar_List.collect
            (fun uu____1061  ->
               match uu____1061 with
               | (t1,uu____1069) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1070,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1078) ->
          let uu____1079 = free_type_vars env t1  in
          let uu____1082 = free_type_vars env t2  in
          FStar_List.append uu____1079 uu____1082
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1087 = free_type_vars_b env b  in
          (match uu____1087 with
           | (env1,f) ->
               let uu____1102 = free_type_vars env1 t1  in
               FStar_List.append f uu____1102)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1119 =
            FStar_List.fold_left
              (fun uu____1143  ->
                 fun bt  ->
                   match uu____1143 with
                   | (env1,free) ->
                       let uu____1167 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1182 = free_type_vars env1 body  in
                             (env1, uu____1182)
                          in
                       (match uu____1167 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1119 with
           | (env1,free) ->
               let uu____1211 = free_type_vars env1 body  in
               FStar_List.append free uu____1211)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1220 =
            FStar_List.fold_left
              (fun uu____1240  ->
                 fun binder  ->
                   match uu____1240 with
                   | (env1,free) ->
                       let uu____1260 = free_type_vars_b env1 binder  in
                       (match uu____1260 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1220 with
           | (env1,free) ->
               let uu____1291 = free_type_vars env1 body  in
               FStar_List.append free uu____1291)
      | FStar_Parser_AST.Project (t1,uu____1295) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1306 = free_type_vars env rel  in
          let uu____1309 =
            let uu____1312 = free_type_vars env init  in
            let uu____1315 =
              FStar_List.collect
                (fun uu____1324  ->
                   match uu____1324 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1330 = free_type_vars env rel1  in
                       let uu____1333 =
                         let uu____1336 = free_type_vars env just  in
                         let uu____1339 = free_type_vars env next  in
                         FStar_List.append uu____1336 uu____1339  in
                       FStar_List.append uu____1330 uu____1333) steps
               in
            FStar_List.append uu____1312 uu____1315  in
          FStar_List.append uu____1306 uu____1309
      | FStar_Parser_AST.Abs uu____1342 -> []
      | FStar_Parser_AST.Let uu____1349 -> []
      | FStar_Parser_AST.LetOpen uu____1370 -> []
      | FStar_Parser_AST.If uu____1375 -> []
      | FStar_Parser_AST.QForall uu____1382 -> []
      | FStar_Parser_AST.QExists uu____1401 -> []
      | FStar_Parser_AST.Record uu____1420 -> []
      | FStar_Parser_AST.Match uu____1433 -> []
      | FStar_Parser_AST.TryWith uu____1448 -> []
      | FStar_Parser_AST.Bind uu____1463 -> []
      | FStar_Parser_AST.Quote uu____1470 -> []
      | FStar_Parser_AST.VQuote uu____1475 -> []
      | FStar_Parser_AST.Antiquote uu____1476 -> []
      | FStar_Parser_AST.Seq uu____1477 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1531 =
        let uu____1532 = unparen t1  in uu____1532.FStar_Parser_AST.tm  in
      match uu____1531 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1574 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1599 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1599  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1622 =
                     let uu____1623 =
                       let uu____1628 =
                         let uu____1629 = FStar_Ident.range_of_id x  in
                         tm_type uu____1629  in
                       (x, uu____1628)  in
                     FStar_Parser_AST.TAnnotated uu____1623  in
                   let uu____1630 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1622 uu____1630
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
        let uu____1648 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1648  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1671 =
                     let uu____1672 =
                       let uu____1677 =
                         let uu____1678 = FStar_Ident.range_of_id x  in
                         tm_type uu____1678  in
                       (x, uu____1677)  in
                     FStar_Parser_AST.TAnnotated uu____1672  in
                   let uu____1679 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1671 uu____1679
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1681 =
             let uu____1682 = unparen t  in uu____1682.FStar_Parser_AST.tm
              in
           match uu____1681 with
           | FStar_Parser_AST.Product uu____1683 -> t
           | uu____1690 ->
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
      | uu____1727 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1738 -> true
    | FStar_Parser_AST.PatTvar (uu____1742,uu____1743) -> true
    | FStar_Parser_AST.PatVar (uu____1749,uu____1750) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1757) -> is_var_pattern p1
    | uu____1770 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1781) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1794;
           FStar_Parser_AST.prange = uu____1795;_},uu____1796)
        -> true
    | uu____1808 -> false
  
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
               ((unit_ty p.FStar_Parser_AST.prange),
                 FStar_Pervasives_Native.None))) p.FStar_Parser_AST.prange
    | uu____1824 -> p
  
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
            let uu____1897 = destruct_app_pattern env is_top_level p1  in
            (match uu____1897 with
             | (name,args,uu____1940) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1990);
               FStar_Parser_AST.prange = uu____1991;_},args)
            when is_top_level ->
            let uu____2001 =
              let uu____2006 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____2006  in
            (uu____2001, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____2028);
               FStar_Parser_AST.prange = uu____2029;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____2059 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2111 -> acc
      | FStar_Parser_AST.PatConst uu____2114 -> acc
      | FStar_Parser_AST.PatName uu____2115 -> acc
      | FStar_Parser_AST.PatOp uu____2116 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2124) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2130) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2139) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2156 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2156
      | FStar_Parser_AST.PatAscribed (pat,uu____2164) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2192 =
             let uu____2194 = FStar_Ident.text_of_id id1  in
             let uu____2196 = FStar_Ident.text_of_id id2  in
             uu____2194 = uu____2196  in
           if uu____2192 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2244 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2285 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2333,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2334))
        -> true
    | uu____2337 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2348  ->
    match uu___3_2348 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2355 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2388  ->
    match uu____2388 with
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
      let uu____2470 =
        let uu____2487 =
          let uu____2490 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2490  in
        let uu____2491 =
          let uu____2502 =
            let uu____2511 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2511)  in
          [uu____2502]  in
        (uu____2487, uu____2491)  in
      FStar_Syntax_Syntax.Tm_app uu____2470  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2560 =
        let uu____2577 =
          let uu____2580 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2580  in
        let uu____2581 =
          let uu____2592 =
            let uu____2601 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2601)  in
          [uu____2592]  in
        (uu____2577, uu____2581)  in
      FStar_Syntax_Syntax.Tm_app uu____2560  in
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
          let uu____2664 =
            let uu____2681 =
              let uu____2684 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2684  in
            let uu____2685 =
              let uu____2696 =
                let uu____2705 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2705)  in
              let uu____2713 =
                let uu____2724 =
                  let uu____2733 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2733)  in
                [uu____2724]  in
              uu____2696 :: uu____2713  in
            (uu____2681, uu____2685)  in
          FStar_Syntax_Syntax.Tm_app uu____2664  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2793 =
        let uu____2808 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2827  ->
               match uu____2827 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2838;
                    FStar_Syntax_Syntax.index = uu____2839;
                    FStar_Syntax_Syntax.sort = t;_},uu____2841)
                   ->
                   let uu____2849 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2849) uu____2808
         in
      FStar_All.pipe_right bs uu____2793  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2865 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2883 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2911 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2932,uu____2933,bs,t,uu____2936,uu____2937)
                            ->
                            let uu____2946 = bs_univnames bs  in
                            let uu____2949 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2946 uu____2949
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2952,uu____2953,t,uu____2955,uu____2956,uu____2957)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2964 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2911 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___589_2973 = s  in
        let uu____2974 =
          let uu____2975 =
            let uu____2984 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3002,bs,t,lids1,lids2) ->
                          let uu___600_3015 = se  in
                          let uu____3016 =
                            let uu____3017 =
                              let uu____3034 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3035 =
                                let uu____3036 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3036 t  in
                              (lid, uvs, uu____3034, uu____3035, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3017
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3016;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___600_3015.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___600_3015.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___600_3015.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___600_3015.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___600_3015.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3050,t,tlid,n,lids1) ->
                          let uu___610_3061 = se  in
                          let uu____3062 =
                            let uu____3063 =
                              let uu____3079 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3079, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3063  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3062;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___610_3061.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___610_3061.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___610_3061.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___610_3061.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___610_3061.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3083 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2984, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2975  in
        {
          FStar_Syntax_Syntax.sigel = uu____2974;
          FStar_Syntax_Syntax.sigrng =
            (uu___589_2973.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___589_2973.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___589_2973.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___589_2973.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___589_2973.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3090,t) ->
        let uvs =
          let uu____3093 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3093 FStar_Util.set_elements  in
        let uu___619_3098 = s  in
        let uu____3099 =
          let uu____3100 =
            let uu____3107 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3107)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3100  in
        {
          FStar_Syntax_Syntax.sigel = uu____3099;
          FStar_Syntax_Syntax.sigrng =
            (uu___619_3098.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___619_3098.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___619_3098.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___619_3098.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___619_3098.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3131 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3134 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3141) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3174,(FStar_Util.Inl t,uu____3176),uu____3177)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3224,(FStar_Util.Inr c,uu____3226),uu____3227)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3274 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3276) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3297,(FStar_Util.Inl t,uu____3299),uu____3300) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3347,(FStar_Util.Inr c,uu____3349),uu____3350) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3397 -> empty_set  in
          FStar_Util.set_union uu____3131 uu____3134  in
        let all_lb_univs =
          let uu____3401 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3417 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3417) empty_set)
             in
          FStar_All.pipe_right uu____3401 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___678_3427 = s  in
        let uu____3428 =
          let uu____3429 =
            let uu____3436 =
              let uu____3437 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___681_3449 = lb  in
                        let uu____3450 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3453 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___681_3449.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3450;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___681_3449.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3453;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___681_3449.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___681_3449.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3437)  in
            (uu____3436, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3429  in
        {
          FStar_Syntax_Syntax.sigel = uu____3428;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3427.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3427.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3427.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3427.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3427.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3462,fml) ->
        let uvs =
          let uu____3465 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3465 FStar_Util.set_elements  in
        let uu___689_3470 = s  in
        let uu____3471 =
          let uu____3472 =
            let uu____3479 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3479)  in
          FStar_Syntax_Syntax.Sig_assume uu____3472  in
        {
          FStar_Syntax_Syntax.sigel = uu____3471;
          FStar_Syntax_Syntax.sigrng =
            (uu___689_3470.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___689_3470.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___689_3470.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___689_3470.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___689_3470.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3481,bs,c,flags) ->
        let uvs =
          let uu____3490 =
            let uu____3493 = bs_univnames bs  in
            let uu____3496 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3493 uu____3496  in
          FStar_All.pipe_right uu____3490 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___700_3504 = s  in
        let uu____3505 =
          let uu____3506 =
            let uu____3519 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3520 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3519, uu____3520, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3506  in
        {
          FStar_Syntax_Syntax.sigel = uu____3505;
          FStar_Syntax_Syntax.sigrng =
            (uu___700_3504.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___700_3504.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___700_3504.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___700_3504.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___700_3504.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___707_3538 = s  in
        let uu____3539 =
          let uu____3540 =
            let uu____3553 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3553)  in
          FStar_Syntax_Syntax.Sig_fail uu____3540  in
        {
          FStar_Syntax_Syntax.sigel = uu____3539;
          FStar_Syntax_Syntax.sigrng =
            (uu___707_3538.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___707_3538.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___707_3538.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___707_3538.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___707_3538.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3562 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3563 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3564 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3565 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3576 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3583 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3591  ->
    match uu___4_3591 with
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
    | uu____3640 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3661 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3661)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3687 =
      let uu____3688 = unparen t  in uu____3688.FStar_Parser_AST.tm  in
    match uu____3687 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3698)) ->
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
             let uu____3789 = sum_to_universe u n  in
             FStar_Util.Inr uu____3789
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3806 = sum_to_universe u n  in
             FStar_Util.Inr uu____3806
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3822 =
               let uu____3828 =
                 let uu____3830 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3830
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3828)
                in
             FStar_Errors.raise_error uu____3822 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3839 ->
        let rec aux t1 univargs =
          let uu____3876 =
            let uu____3877 = unparen t1  in uu____3877.FStar_Parser_AST.tm
             in
          match uu____3876 with
          | FStar_Parser_AST.App (t2,targ,uu____3885) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3912  ->
                     match uu___5_3912 with
                     | FStar_Util.Inr uu____3919 -> true
                     | uu____3922 -> false) univargs
              then
                let uu____3930 =
                  let uu____3931 =
                    FStar_List.map
                      (fun uu___6_3941  ->
                         match uu___6_3941 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3931  in
                FStar_Util.Inr uu____3930
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3967  ->
                        match uu___7_3967 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3977 -> failwith "impossible")
                     univargs
                    in
                 let uu____3981 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3981)
          | uu____3997 ->
              let uu____3998 =
                let uu____4004 =
                  let uu____4006 =
                    let uu____4008 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4008 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4006  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4004)  in
              FStar_Errors.raise_error uu____3998 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4023 ->
        let uu____4024 =
          let uu____4030 =
            let uu____4032 =
              let uu____4034 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4034 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4032  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4030)  in
        FStar_Errors.raise_error uu____4024 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4075;_});
            FStar_Syntax_Syntax.pos = uu____4076;
            FStar_Syntax_Syntax.vars = uu____4077;_})::uu____4078
        ->
        let uu____4109 =
          let uu____4115 =
            let uu____4117 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4117
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4115)  in
        FStar_Errors.raise_error uu____4109 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4123 ->
        let uu____4142 =
          let uu____4148 =
            let uu____4150 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4150
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4148)  in
        FStar_Errors.raise_error uu____4142 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4163 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4163) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4191 = FStar_List.hd fields  in
        match uu____4191 with
        | (f,uu____4201) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4212 =
              match uu____4212 with
              | (f',uu____4218) ->
                  let uu____4219 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4219
                  then ()
                  else
                    (let msg =
                       let uu____4226 = FStar_Ident.string_of_lid f  in
                       let uu____4228 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4230 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4226 uu____4228 uu____4230
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4235 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4235);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4283 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4290 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4291 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4293,pats1) ->
            let aux out uu____4334 =
              match uu____4334 with
              | (p1,uu____4347) ->
                  let intersection =
                    let uu____4357 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4357 out  in
                  let uu____4360 = FStar_Util.set_is_empty intersection  in
                  if uu____4360
                  then
                    let uu____4365 = pat_vars p1  in
                    FStar_Util.set_union out uu____4365
                  else
                    (let duplicate_bv =
                       let uu____4371 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4371  in
                     let uu____4374 =
                       let uu____4380 =
                         let uu____4382 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4382
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4380)
                        in
                     FStar_Errors.raise_error uu____4374 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4406 = pat_vars p  in
          FStar_All.pipe_right uu____4406 (fun uu____4411  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4435 =
              let uu____4437 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4437  in
            if uu____4435
            then ()
            else
              (let nonlinear_vars =
                 let uu____4446 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4446  in
               let first_nonlinear_var =
                 let uu____4450 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4450  in
               let uu____4453 =
                 let uu____4459 =
                   let uu____4461 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4461
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4459)  in
               FStar_Errors.raise_error uu____4453 r)
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
          let uu____4788 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4795 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4797 = FStar_Ident.text_of_id x  in
                 uu____4795 = uu____4797) l
             in
          match uu____4788 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4811 ->
              let uu____4814 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4814 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4955 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4977 =
                  let uu____4983 =
                    let uu____4985 = FStar_Ident.text_of_id op  in
                    let uu____4987 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4985
                      uu____4987
                     in
                  let uu____4989 = FStar_Ident.range_of_id op  in
                  (uu____4983, uu____4989)  in
                FStar_Ident.mk_ident uu____4977  in
              let p2 =
                let uu___934_4992 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_4992.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5009 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5012 = aux loc env1 p2  in
                match uu____5012 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5068 =
                      match binder with
                      | LetBinder uu____5089 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5114 = close_fun env1 t  in
                            desugar_term env1 uu____5114  in
                          let x1 =
                            let uu___960_5116 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5116.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5116.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5068 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5162 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5163 -> ()
                           | uu____5164 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5165 ->
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
              let uu____5183 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5183, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5196 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5196, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5214 = resolvex loc env1 x  in
              (match uu____5214 with
               | (loc1,env2,xbv) ->
                   let uu____5246 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5246, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5264 = resolvex loc env1 x  in
              (match uu____5264 with
               | (loc1,env2,xbv) ->
                   let uu____5296 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5296, []))
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
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5310, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5338;_},args)
              ->
              let uu____5344 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5405  ->
                       match uu____5405 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5486 = aux loc1 env2 arg  in
                           (match uu____5486 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5344 with
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
                   let uu____5658 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5658, annots))
          | FStar_Parser_AST.PatApp uu____5674 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5702 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5752  ->
                       match uu____5752 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5813 = aux loc1 env2 pat  in
                           (match uu____5813 with
                            | (loc2,env3,uu____5852,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5702 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5946 =
                       let uu____5949 =
                         let uu____5956 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5956  in
                       let uu____5957 =
                         let uu____5958 =
                           let uu____5972 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5972, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5958  in
                       FStar_All.pipe_left uu____5949 uu____5957  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6006 =
                              let uu____6007 =
                                let uu____6021 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6021, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6007  in
                            FStar_All.pipe_left (pos_r r) uu____6006) pats1
                       uu____5946
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
              let uu____6077 =
                FStar_List.fold_left
                  (fun uu____6136  ->
                     fun p2  ->
                       match uu____6136 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6218 = aux loc1 env2 p2  in
                           (match uu____6218 with
                            | (loc2,env3,uu____6262,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6077 with
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
                     | uu____6425 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6428 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6428, annots))
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
                     (fun uu____6505  ->
                        match uu____6505 with
                        | (f,p2) ->
                            let uu____6516 = FStar_Ident.ident_of_lid f  in
                            (uu____6516, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6536  ->
                        match uu____6536 with
                        | (f,uu____6542) ->
                            let uu____6543 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6571  ->
                                      match uu____6571 with
                                      | (g,uu____6578) ->
                                          let uu____6579 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6581 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6579 = uu____6581))
                               in
                            (match uu____6543 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6588,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6595 =
                  let uu____6596 =
                    let uu____6603 =
                      let uu____6604 =
                        let uu____6605 =
                          let uu____6606 =
                            let uu____6607 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6607
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6606  in
                        FStar_Parser_AST.PatName uu____6605  in
                      FStar_Parser_AST.mk_pattern uu____6604
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6603, args)  in
                  FStar_Parser_AST.PatApp uu____6596  in
                FStar_Parser_AST.mk_pattern uu____6595
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6612 = aux loc env1 app  in
              (match uu____6612 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6689 =
                           let uu____6690 =
                             let uu____6704 =
                               let uu___1110_6705 = fv  in
                               let uu____6706 =
                                 let uu____6709 =
                                   let uu____6710 =
                                     let uu____6717 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6717)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6710
                                    in
                                 FStar_Pervasives_Native.Some uu____6709  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6705.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6705.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6706
                               }  in
                             (uu____6704, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6690  in
                         FStar_All.pipe_left pos uu____6689
                     | uu____6743 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6827 = aux' true loc env1 p2  in
              (match uu____6827 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6880 =
                     FStar_List.fold_left
                       (fun uu____6928  ->
                          fun p4  ->
                            match uu____6928 with
                            | (loc2,env3,ps1) ->
                                let uu____6993 = aux' true loc2 env3 p4  in
                                (match uu____6993 with
                                 | (loc3,env4,uu____7031,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6880 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7192 ->
              let uu____7193 = aux' true loc env1 p1  in
              (match uu____7193 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7284 = aux_maybe_or env p  in
        match uu____7284 with
        | (env1,b,pats) ->
            ((let uu____7339 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7339
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
            let uu____7413 =
              let uu____7414 =
                let uu____7425 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7425, (ty, tacopt))  in
              LetBinder uu____7414  in
            (env, uu____7413, [])  in
          let op_to_ident x =
            let uu____7442 =
              let uu____7448 =
                let uu____7450 = FStar_Ident.text_of_id x  in
                let uu____7452 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7450
                  uu____7452
                 in
              let uu____7454 = FStar_Ident.range_of_id x  in
              (uu____7448, uu____7454)  in
            FStar_Ident.mk_ident uu____7442  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7465 = op_to_ident x  in
              mklet uu____7465 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7467) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7473;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7489 = op_to_ident x  in
              let uu____7490 = desugar_term env t  in
              mklet uu____7489 uu____7490 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7492);
                 FStar_Parser_AST.prange = uu____7493;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7513 = desugar_term env t  in
              mklet x uu____7513 tacopt1
          | uu____7514 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7527 = desugar_data_pat true env p  in
           match uu____7527 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7557;
                      FStar_Syntax_Syntax.p = uu____7558;_},uu____7559)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7572;
                      FStar_Syntax_Syntax.p = uu____7573;_},uu____7574)::[]
                     -> []
                 | uu____7587 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7595  ->
    fun env  ->
      fun pat  ->
        let uu____7599 = desugar_data_pat false env pat  in
        match uu____7599 with | (env1,uu____7616,pat1) -> (env1, pat1)

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
      let uu____7638 = desugar_term_aq env e  in
      match uu____7638 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7657 = desugar_typ_aq env e  in
      match uu____7657 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7667  ->
        fun range  ->
          match uu____7667 with
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
              ((let uu____7689 =
                  let uu____7691 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7691  in
                if uu____7689
                then
                  let uu____7694 =
                    let uu____7700 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7700)  in
                  FStar_Errors.log_issue range uu____7694
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
                  let uu____7721 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7721 range  in
                let lid1 =
                  let uu____7725 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7725 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7735 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7735 range  in
                           let private_fv =
                             let uu____7737 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7737 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7738 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7738.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7738.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7739 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7743 =
                        let uu____7749 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7749)
                         in
                      FStar_Errors.raise_error uu____7743 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7769 =
                  let uu____7776 =
                    let uu____7777 =
                      let uu____7794 =
                        let uu____7805 =
                          let uu____7814 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7814)  in
                        [uu____7805]  in
                      (lid1, uu____7794)  in
                    FStar_Syntax_Syntax.Tm_app uu____7777  in
                  FStar_Syntax_Syntax.mk uu____7776  in
                uu____7769 FStar_Pervasives_Native.None range))

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
          let uu___1293_7933 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7933.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7933.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7936 =
          let uu____7937 = unparen top  in uu____7937.FStar_Parser_AST.tm  in
        match uu____7936 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7942 ->
            let uu____7951 = desugar_formula env top  in (uu____7951, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7960 = desugar_formula env t  in (uu____7960, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7969 = desugar_formula env t  in (uu____7969, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7996 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7996, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7998 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7998, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8005 = FStar_Ident.text_of_id id  in uu____8005 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8011 =
                let uu____8012 =
                  let uu____8019 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8019, args)  in
                FStar_Parser_AST.Op uu____8012  in
              FStar_Parser_AST.mk_term uu____8011 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8024 =
              let uu____8025 =
                let uu____8026 =
                  let uu____8033 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8033, [e])  in
                FStar_Parser_AST.Op uu____8026  in
              FStar_Parser_AST.mk_term uu____8025 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8024
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8045 = FStar_Ident.text_of_id op_star  in
             uu____8045 = "*") &&
              (let uu____8050 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____8050 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8074 = FStar_Ident.text_of_id id  in
                   uu____8074 = "*") &&
                    (let uu____8079 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____8079 FStar_Option.isNone)
                  ->
                  let uu____8086 = flatten t1  in
                  FStar_List.append uu____8086 [t2]
              | uu____8089 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1338_8094 = top  in
              let uu____8095 =
                let uu____8096 =
                  let uu____8107 =
                    FStar_List.map
                      (fun uu____8118  -> FStar_Util.Inr uu____8118) terms
                     in
                  (uu____8107, rhs)  in
                FStar_Parser_AST.Sum uu____8096  in
              {
                FStar_Parser_AST.tm = uu____8095;
                FStar_Parser_AST.range =
                  (uu___1338_8094.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1338_8094.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8126 =
              let uu____8127 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8127  in
            (uu____8126, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8133 =
              let uu____8139 =
                let uu____8141 =
                  let uu____8143 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8143 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8141  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8139)  in
            FStar_Errors.raise_error uu____8133 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8158 = op_as_term env (FStar_List.length args) s  in
            (match uu____8158 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8165 =
                   let uu____8171 =
                     let uu____8173 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8173
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8171)
                    in
                 FStar_Errors.raise_error uu____8165
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8188 =
                     let uu____8213 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8275 = desugar_term_aq env t  in
                               match uu____8275 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8213 FStar_List.unzip  in
                   (match uu____8188 with
                    | (args1,aqs) ->
                        let uu____8408 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8408, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8425)::[]) when
            let uu____8440 = FStar_Ident.string_of_lid n  in
            uu____8440 = "SMTPat" ->
            let uu____8444 =
              let uu___1367_8445 = top  in
              let uu____8446 =
                let uu____8447 =
                  let uu____8454 =
                    let uu___1369_8455 = top  in
                    let uu____8456 =
                      let uu____8457 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8457  in
                    {
                      FStar_Parser_AST.tm = uu____8456;
                      FStar_Parser_AST.range =
                        (uu___1369_8455.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1369_8455.FStar_Parser_AST.level)
                    }  in
                  (uu____8454, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8447  in
              {
                FStar_Parser_AST.tm = uu____8446;
                FStar_Parser_AST.range =
                  (uu___1367_8445.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1367_8445.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8444
        | FStar_Parser_AST.Construct (n,(a,uu____8460)::[]) when
            let uu____8475 = FStar_Ident.string_of_lid n  in
            uu____8475 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8482 =
                let uu___1379_8483 = top  in
                let uu____8484 =
                  let uu____8485 =
                    let uu____8492 =
                      let uu___1381_8493 = top  in
                      let uu____8494 =
                        let uu____8495 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8495  in
                      {
                        FStar_Parser_AST.tm = uu____8494;
                        FStar_Parser_AST.range =
                          (uu___1381_8493.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1381_8493.FStar_Parser_AST.level)
                      }  in
                    (uu____8492, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8485  in
                {
                  FStar_Parser_AST.tm = uu____8484;
                  FStar_Parser_AST.range =
                    (uu___1379_8483.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1379_8483.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8482))
        | FStar_Parser_AST.Construct (n,(a,uu____8498)::[]) when
            let uu____8513 = FStar_Ident.string_of_lid n  in
            uu____8513 = "SMTPatOr" ->
            let uu____8517 =
              let uu___1390_8518 = top  in
              let uu____8519 =
                let uu____8520 =
                  let uu____8527 =
                    let uu___1392_8528 = top  in
                    let uu____8529 =
                      let uu____8530 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8530  in
                    {
                      FStar_Parser_AST.tm = uu____8529;
                      FStar_Parser_AST.range =
                        (uu___1392_8528.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1392_8528.FStar_Parser_AST.level)
                    }  in
                  (uu____8527, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8520  in
              {
                FStar_Parser_AST.tm = uu____8519;
                FStar_Parser_AST.range =
                  (uu___1390_8518.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1390_8518.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8517
        | FStar_Parser_AST.Name lid when
            let uu____8532 = FStar_Ident.string_of_lid lid  in
            uu____8532 = "Type0" ->
            let uu____8536 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8536, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8538 = FStar_Ident.string_of_lid lid  in
            uu____8538 = "Type" ->
            let uu____8542 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8542, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8559 = FStar_Ident.string_of_lid lid  in
            uu____8559 = "Type" ->
            let uu____8563 =
              let uu____8564 =
                let uu____8565 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8565  in
              mk uu____8564  in
            (uu____8563, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8567 = FStar_Ident.string_of_lid lid  in
            uu____8567 = "Effect" ->
            let uu____8571 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8571, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8573 = FStar_Ident.string_of_lid lid  in
            uu____8573 = "True" ->
            let uu____8577 =
              let uu____8578 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8578
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8577, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8580 = FStar_Ident.string_of_lid lid  in
            uu____8580 = "False" ->
            let uu____8584 =
              let uu____8585 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8585
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8584, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8590 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8590) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8594 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8594 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8603 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8603, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8605 =
                   let uu____8607 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8607 txt
                    in
                 failwith uu____8605)
        | FStar_Parser_AST.Var l ->
            let uu____8615 = desugar_name mk setpos env true l  in
            (uu____8615, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8623 = desugar_name mk setpos env true l  in
            (uu____8623, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8640 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8640 with
              | FStar_Pervasives_Native.Some uu____8650 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8658 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8658 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8676 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8697 =
                   let uu____8698 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8698  in
                 (uu____8697, noaqs)
             | uu____8704 ->
                 let uu____8712 =
                   let uu____8718 =
                     let uu____8720 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8720
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8718)  in
                 FStar_Errors.raise_error uu____8712
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8729 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8729 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8736 =
                   let uu____8742 =
                     let uu____8744 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8744
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8742)
                    in
                 FStar_Errors.raise_error uu____8736
                   top.FStar_Parser_AST.range
             | uu____8752 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8756 = desugar_name mk setpos env true lid'  in
                 (uu____8756, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8777 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8777 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8796 ->
                      let uu____8803 =
                        FStar_Util.take
                          (fun uu____8827  ->
                             match uu____8827 with
                             | (uu____8833,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8803 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8878 =
                             let uu____8903 =
                               FStar_List.map
                                 (fun uu____8946  ->
                                    match uu____8946 with
                                    | (t,imp) ->
                                        let uu____8963 =
                                          desugar_term_aq env t  in
                                        (match uu____8963 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8903 FStar_List.unzip
                              in
                           (match uu____8878 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9106 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9106, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9125 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9125 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9133 =
                         let uu____9135 =
                           let uu____9137 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9137 " not found"  in
                         Prims.op_Hat "Constructor " uu____9135  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9133)
                   | FStar_Pervasives_Native.Some uu____9142 ->
                       let uu____9143 =
                         let uu____9145 =
                           let uu____9147 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9147
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9145  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9143)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9176  ->
                 match uu___8_9176 with
                 | FStar_Util.Inr uu____9182 -> true
                 | uu____9184 -> false) binders
            ->
            let terms =
              let uu____9193 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9210  ->
                        match uu___9_9210 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9216 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9193 [t]  in
            let uu____9218 =
              let uu____9243 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9300 = desugar_typ_aq env t1  in
                        match uu____9300 with
                        | (t',aq) ->
                            let uu____9311 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9311, aq)))
                 in
              FStar_All.pipe_right uu____9243 FStar_List.unzip  in
            (match uu____9218 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9421 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9421
                    in
                 let uu____9430 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9430, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9457 =
              let uu____9474 =
                let uu____9481 =
                  let uu____9488 =
                    FStar_All.pipe_left
                      (fun uu____9497  -> FStar_Util.Inl uu____9497)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9488]  in
                FStar_List.append binders uu____9481  in
              FStar_List.fold_left
                (fun uu____9542  ->
                   fun b  ->
                     match uu____9542 with
                     | (env1,tparams,typs) ->
                         let uu____9603 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9618 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9618)
                            in
                         (match uu____9603 with
                          | (xopt,t1) ->
                              let uu____9643 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9652 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9652)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9643 with
                               | (env2,x) ->
                                   let uu____9672 =
                                     let uu____9675 =
                                       let uu____9678 =
                                         let uu____9679 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9679
                                          in
                                       [uu____9678]  in
                                     FStar_List.append typs uu____9675  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1521_9705 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1521_9705.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1521_9705.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9672)))) (env, [], []) uu____9474
               in
            (match uu____9457 with
             | (env1,uu____9733,targs) ->
                 let tup =
                   let uu____9756 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9756
                    in
                 let uu____9757 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9757, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9776 = uncurry binders t  in
            (match uu____9776 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9820 =
                   match uu___10_9820 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9837 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9837
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9861 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9861 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9894 = aux env [] bs  in (uu____9894, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9903 = desugar_binder env b  in
            (match uu____9903 with
             | (FStar_Pervasives_Native.None ,uu____9914) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9929 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9929 with
                  | ((x,uu____9945),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9958 =
                        let uu____9959 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9959  in
                      (uu____9958, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10037 = FStar_Util.set_is_empty i  in
                    if uu____10037
                    then
                      let uu____10042 = FStar_Util.set_union acc set  in
                      aux uu____10042 sets2
                    else
                      (let uu____10047 =
                         let uu____10048 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10048  in
                       FStar_Pervasives_Native.Some uu____10047)
                 in
              let uu____10051 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10051 sets  in
            ((let uu____10055 = check_disjoint bvss  in
              match uu____10055 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10059 =
                    let uu____10065 =
                      let uu____10067 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10067
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10065)
                     in
                  let uu____10071 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10059 uu____10071);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10079 =
                FStar_List.fold_left
                  (fun uu____10099  ->
                     fun pat  ->
                       match uu____10099 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10125,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10135 =
                                  let uu____10138 = free_type_vars env1 t  in
                                  FStar_List.append uu____10138 ftvs  in
                                (env1, uu____10135)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10143,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10154 =
                                  let uu____10157 = free_type_vars env1 t  in
                                  let uu____10160 =
                                    let uu____10163 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10163 ftvs  in
                                  FStar_List.append uu____10157 uu____10160
                                   in
                                (env1, uu____10154)
                            | uu____10168 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10079 with
              | (uu____10177,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10189 =
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
                    FStar_List.append uu____10189 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10269 = desugar_term_aq env1 body  in
                        (match uu____10269 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10304 =
                                       let uu____10305 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10305
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10304
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
                             let uu____10374 =
                               let uu____10375 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10375  in
                             (uu____10374, aq))
                    | p::rest ->
                        let uu____10388 = desugar_binding_pat env1 p  in
                        (match uu____10388 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10420)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10435 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10444 =
                               match b with
                               | LetBinder uu____10485 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10554) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10608 =
                                           let uu____10617 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10617, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10608
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10679,uu____10680) ->
                                              let tup2 =
                                                let uu____10682 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10682
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10687 =
                                                  let uu____10694 =
                                                    let uu____10695 =
                                                      let uu____10712 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10715 =
                                                        let uu____10726 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10735 =
                                                          let uu____10746 =
                                                            let uu____10755 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10755
                                                             in
                                                          [uu____10746]  in
                                                        uu____10726 ::
                                                          uu____10735
                                                         in
                                                      (uu____10712,
                                                        uu____10715)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10695
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10694
                                                   in
                                                uu____10687
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10803 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10803
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10854,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10856,pats1)) ->
                                              let tupn =
                                                let uu____10901 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10901
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10914 =
                                                  let uu____10915 =
                                                    let uu____10932 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10935 =
                                                      let uu____10946 =
                                                        let uu____10957 =
                                                          let uu____10966 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10966
                                                           in
                                                        [uu____10957]  in
                                                      FStar_List.append args
                                                        uu____10946
                                                       in
                                                    (uu____10932,
                                                      uu____10935)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10915
                                                   in
                                                mk uu____10914  in
                                              let p2 =
                                                let uu____11014 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11014
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11061 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10444 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11153,uu____11154,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11176 =
                let uu____11177 = unparen e  in
                uu____11177.FStar_Parser_AST.tm  in
              match uu____11176 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11187 ->
                  let uu____11188 = desugar_term_aq env e  in
                  (match uu____11188 with
                   | (head,aq) ->
                       let uu____11201 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11201, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11208 ->
            let rec aux args aqs e =
              let uu____11285 =
                let uu____11286 = unparen e  in
                uu____11286.FStar_Parser_AST.tm  in
              match uu____11285 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11304 = desugar_term_aq env t  in
                  (match uu____11304 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11352 ->
                  let uu____11353 = desugar_term_aq env e  in
                  (match uu____11353 with
                   | (head,aq) ->
                       let uu____11374 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11374, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11427 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11427
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11434 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11434  in
            let bind =
              let uu____11439 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11439 FStar_Parser_AST.Expr
               in
            let uu____11440 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11440
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
            let uu____11492 = desugar_term_aq env t  in
            (match uu____11492 with
             | (tm,s) ->
                 let uu____11503 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11503, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11509 =
              let uu____11522 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11522 then desugar_typ_aq else desugar_term_aq  in
            uu____11509 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11589 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11732  ->
                        match uu____11732 with
                        | (attr_opt,(p,def)) ->
                            let uu____11790 = is_app_pattern p  in
                            if uu____11790
                            then
                              let uu____11823 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11823, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11906 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11906, def1)
                               | uu____11951 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11989);
                                           FStar_Parser_AST.prange =
                                             uu____11990;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12039 =
                                            let uu____12060 =
                                              let uu____12065 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12065  in
                                            (uu____12060, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12039, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12157) ->
                                        if top_level
                                        then
                                          let uu____12193 =
                                            let uu____12214 =
                                              let uu____12219 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12219  in
                                            (uu____12214, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12193, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12310 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12343 =
                FStar_List.fold_left
                  (fun uu____12432  ->
                     fun uu____12433  ->
                       match (uu____12432, uu____12433) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12563,uu____12564),uu____12565))
                           ->
                           let uu____12699 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12739 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12739 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12774 =
                                        let uu____12777 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12777 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12774, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12793 =
                                   let uu____12801 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12801
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12793 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12699 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12343 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13047 =
                    match uu____13047 with
                    | (attrs_opt,(uu____13087,args,result_t),def) ->
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
                                let uu____13179 = is_comp_type env1 t  in
                                if uu____13179
                                then
                                  ((let uu____13183 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13193 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13193))
                                       in
                                    match uu____13183 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13200 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13203 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13203))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13200
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
                          | uu____13214 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13217 = desugar_term_aq env1 def2  in
                        (match uu____13217 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13239 =
                                     let uu____13240 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13240
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13239
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
                  let uu____13281 =
                    let uu____13298 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13298 FStar_List.unzip  in
                  (match uu____13281 with
                   | (lbs1,aqss) ->
                       let uu____13440 = desugar_term_aq env' body  in
                       (match uu____13440 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13546  ->
                                    fun used_marker  ->
                                      match uu____13546 with
                                      | (_attr_opt,(f,uu____13620,uu____13621),uu____13622)
                                          ->
                                          let uu____13679 =
                                            let uu____13681 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13681  in
                                          if uu____13679
                                          then
                                            let uu____13705 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13723 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13725 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13723, "Local",
                                                    uu____13725)
                                              | FStar_Util.Inr l ->
                                                  let uu____13730 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13732 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13730, "Global",
                                                    uu____13732)
                                               in
                                            (match uu____13705 with
                                             | (nm,gl,rng) ->
                                                 let uu____13743 =
                                                   let uu____13749 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13749)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13743)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13757 =
                                let uu____13760 =
                                  let uu____13761 =
                                    let uu____13775 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13775)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13761  in
                                FStar_All.pipe_left mk uu____13760  in
                              (uu____13757,
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
              let uu____13877 = desugar_term_aq env t1  in
              match uu____13877 with
              | (t11,aq0) ->
                  let uu____13898 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13898 with
                   | (env1,binder,pat1) ->
                       let uu____13928 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13970 = desugar_term_aq env1 t2  in
                             (match uu____13970 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13992 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13992
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13993 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13993, aq))
                         | LocalBinder (x,uu____14034) ->
                             let uu____14035 = desugar_term_aq env1 t2  in
                             (match uu____14035 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14057;
                                         FStar_Syntax_Syntax.p = uu____14058;_},uu____14059)::[]
                                        -> body1
                                    | uu____14072 ->
                                        let uu____14075 =
                                          let uu____14082 =
                                            let uu____14083 =
                                              let uu____14106 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14109 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14106, uu____14109)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14083
                                             in
                                          FStar_Syntax_Syntax.mk uu____14082
                                           in
                                        uu____14075
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14146 =
                                    let uu____14149 =
                                      let uu____14150 =
                                        let uu____14164 =
                                          let uu____14167 =
                                            let uu____14168 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14168]  in
                                          FStar_Syntax_Subst.close
                                            uu____14167 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14164)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14150
                                       in
                                    FStar_All.pipe_left mk uu____14149  in
                                  (uu____14146, aq))
                          in
                       (match uu____13928 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14276 = FStar_List.hd lbs  in
            (match uu____14276 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14320 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14320
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14336 =
                let uu____14337 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14337  in
              mk uu____14336  in
            let uu____14338 = desugar_term_aq env t1  in
            (match uu____14338 with
             | (t1',aq1) ->
                 let uu____14349 = desugar_term_aq env t2  in
                 (match uu____14349 with
                  | (t2',aq2) ->
                      let uu____14360 = desugar_term_aq env t3  in
                      (match uu____14360 with
                       | (t3',aq3) ->
                           let uu____14371 =
                             let uu____14372 =
                               let uu____14373 =
                                 let uu____14396 =
                                   let uu____14413 =
                                     let uu____14428 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14428,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14442 =
                                     let uu____14459 =
                                       let uu____14474 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14474,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14459]  in
                                   uu____14413 :: uu____14442  in
                                 (t1', uu____14396)  in
                               FStar_Syntax_Syntax.Tm_match uu____14373  in
                             mk uu____14372  in
                           (uu____14371, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14670 =
              match uu____14670 with
              | (pat,wopt,b) ->
                  let uu____14692 = desugar_match_pat env pat  in
                  (match uu____14692 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14723 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14723
                          in
                       let uu____14728 = desugar_term_aq env1 b  in
                       (match uu____14728 with
                        | (b1,aq) ->
                            let uu____14741 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14741, aq)))
               in
            let uu____14746 = desugar_term_aq env e  in
            (match uu____14746 with
             | (e1,aq) ->
                 let uu____14757 =
                   let uu____14788 =
                     let uu____14821 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14821 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14788
                     (fun uu____15039  ->
                        match uu____15039 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14757 with
                  | (brs,aqs) ->
                      let uu____15258 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15258, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15292 =
              let uu____15313 = is_comp_type env t  in
              if uu____15313
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15368 = desugar_term_aq env t  in
                 match uu____15368 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15292 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15460 = desugar_term_aq env e  in
                 (match uu____15460 with
                  | (e1,aq) ->
                      let uu____15471 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15471, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15510,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15553 = FStar_List.hd fields  in
              match uu____15553 with
              | (f,uu____15565) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15613  ->
                        match uu____15613 with
                        | (g,uu____15620) ->
                            let uu____15621 = FStar_Ident.text_of_id f  in
                            let uu____15623 =
                              let uu____15625 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15625  in
                            uu____15621 = uu____15623))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15632,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15646 =
                         let uu____15652 =
                           let uu____15654 = FStar_Ident.text_of_id f  in
                           let uu____15656 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15654 uu____15656
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15652)
                          in
                       FStar_Errors.raise_error uu____15646
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
                  let uu____15667 =
                    let uu____15678 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15709  ->
                              match uu____15709 with
                              | (f,uu____15719) ->
                                  let uu____15720 =
                                    let uu____15721 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15721
                                     in
                                  (uu____15720, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15678)  in
                  FStar_Parser_AST.Construct uu____15667
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15739 =
                      let uu____15740 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15740  in
                    let uu____15741 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15739 uu____15741
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15743 =
                      let uu____15756 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15786  ->
                                match uu____15786 with
                                | (f,uu____15796) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15756)  in
                    FStar_Parser_AST.Record uu____15743  in
                  let uu____15805 =
                    let uu____15826 =
                      let uu____15841 =
                        let uu____15854 =
                          let uu____15859 =
                            let uu____15860 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15860
                             in
                          (uu____15859, e)  in
                        (FStar_Pervasives_Native.None, uu____15854)  in
                      [uu____15841]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15826,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15805
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15912 = desugar_term_aq env recterm1  in
            (match uu____15912 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15928;
                         FStar_Syntax_Syntax.vars = uu____15929;_},args)
                      ->
                      let uu____15955 =
                        let uu____15956 =
                          let uu____15957 =
                            let uu____15974 =
                              let uu____15977 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15978 =
                                let uu____15981 =
                                  let uu____15982 =
                                    let uu____15989 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15989)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15982
                                   in
                                FStar_Pervasives_Native.Some uu____15981  in
                              FStar_Syntax_Syntax.fvar uu____15977
                                FStar_Syntax_Syntax.delta_constant
                                uu____15978
                               in
                            (uu____15974, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15957  in
                        FStar_All.pipe_left mk uu____15956  in
                      (uu____15955, s)
                  | uu____16018 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16021 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16021 with
             | (constrname,is_rec) ->
                 let uu____16040 = desugar_term_aq env e  in
                 (match uu____16040 with
                  | (e1,s) ->
                      let projname =
                        let uu____16052 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16052
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16059 =
                            let uu____16060 =
                              let uu____16065 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16065)  in
                            FStar_Syntax_Syntax.Record_projector uu____16060
                             in
                          FStar_Pervasives_Native.Some uu____16059
                        else FStar_Pervasives_Native.None  in
                      let uu____16068 =
                        let uu____16069 =
                          let uu____16070 =
                            let uu____16087 =
                              let uu____16090 =
                                let uu____16091 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16091
                                 in
                              FStar_Syntax_Syntax.fvar uu____16090
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16093 =
                              let uu____16104 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16104]  in
                            (uu____16087, uu____16093)  in
                          FStar_Syntax_Syntax.Tm_app uu____16070  in
                        FStar_All.pipe_left mk uu____16069  in
                      (uu____16068, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16144 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16144
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16155 =
              let uu____16156 = FStar_Syntax_Subst.compress tm  in
              uu____16156.FStar_Syntax_Syntax.n  in
            (match uu____16155 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16164 =
                   let uu___2089_16165 =
                     let uu____16166 =
                       let uu____16168 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16168  in
                     FStar_Syntax_Util.exp_string uu____16166  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2089_16165.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2089_16165.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16164, noaqs)
             | uu____16169 ->
                 let uu____16170 =
                   let uu____16176 =
                     let uu____16178 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16178
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16176)  in
                 FStar_Errors.raise_error uu____16170
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16187 = desugar_term_aq env e  in
            (match uu____16187 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16199 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16199, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16204 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16205 =
              let uu____16206 =
                let uu____16213 = desugar_term env e  in (bv, uu____16213)
                 in
              [uu____16206]  in
            (uu____16204, uu____16205)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16238 =
              let uu____16239 =
                let uu____16240 =
                  let uu____16247 = desugar_term env e  in (uu____16247, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16240  in
              FStar_All.pipe_left mk uu____16239  in
            (uu____16238, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16276 -> false  in
              let uu____16278 =
                let uu____16279 = unparen rel1  in
                uu____16279.FStar_Parser_AST.tm  in
              match uu____16278 with
              | FStar_Parser_AST.Op (id,uu____16282) ->
                  let uu____16287 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16287 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16295 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16295 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16306 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16306 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16312 -> false  in
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
              let uu____16333 =
                let uu____16334 =
                  let uu____16341 =
                    let uu____16342 =
                      let uu____16343 =
                        let uu____16352 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16365 =
                          let uu____16366 =
                            let uu____16367 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16367  in
                          FStar_Parser_AST.mk_term uu____16366
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16352, uu____16365,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16343  in
                    FStar_Parser_AST.mk_term uu____16342
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16341)  in
                FStar_Parser_AST.Abs uu____16334  in
              FStar_Parser_AST.mk_term uu____16333
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
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____16388 = FStar_List.last steps  in
              match uu____16388 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16391,uu____16392,last_expr)) -> last_expr
              | FStar_Pervasives_Native.None  -> init_expr  in
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
                init_expr.FStar_Parser_AST.range
               in
            let uu____16418 =
              FStar_List.fold_left
                (fun uu____16436  ->
                   fun uu____16437  ->
                     match (uu____16436, uu____16437) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16460 = is_impl rel2  in
                           if uu____16460
                           then
                             let uu____16463 =
                               let uu____16470 =
                                 let uu____16475 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16475, FStar_Parser_AST.Nothing)  in
                               [uu____16470]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16463 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16487 =
                             let uu____16494 =
                               let uu____16501 =
                                 let uu____16508 =
                                   let uu____16515 =
                                     let uu____16520 = eta_and_annot rel2  in
                                     (uu____16520, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16521 =
                                     let uu____16528 =
                                       let uu____16535 =
                                         let uu____16540 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16540,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16541 =
                                         let uu____16548 =
                                           let uu____16553 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16553,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16548]  in
                                       uu____16535 :: uu____16541  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16528
                                      in
                                   uu____16515 :: uu____16521  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16508
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16501
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16494
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16487
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16418 with
             | (e1,uu____16591) ->
                 let e2 =
                   let uu____16593 =
                     let uu____16600 =
                       let uu____16607 =
                         let uu____16614 =
                           let uu____16619 = FStar_Parser_AST.thunk e1  in
                           (uu____16619, FStar_Parser_AST.Nothing)  in
                         [uu____16614]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16607  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16600  in
                   FStar_Parser_AST.mkApp finish uu____16593
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16636 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16637 = desugar_formula env top  in
            (uu____16637, noaqs)
        | uu____16638 ->
            let uu____16639 =
              let uu____16645 =
                let uu____16647 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16647  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16645)  in
            FStar_Errors.raise_error uu____16639 top.FStar_Parser_AST.range

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
           (fun uu____16691  ->
              match uu____16691 with
              | (a,imp) ->
                  let uu____16704 = desugar_term env a  in
                  arg_withimp_e imp uu____16704))

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
          let is_requires uu____16741 =
            match uu____16741 with
            | (t1,uu____16748) ->
                let uu____16749 =
                  let uu____16750 = unparen t1  in
                  uu____16750.FStar_Parser_AST.tm  in
                (match uu____16749 with
                 | FStar_Parser_AST.Requires uu____16752 -> true
                 | uu____16761 -> false)
             in
          let is_ensures uu____16773 =
            match uu____16773 with
            | (t1,uu____16780) ->
                let uu____16781 =
                  let uu____16782 = unparen t1  in
                  uu____16782.FStar_Parser_AST.tm  in
                (match uu____16781 with
                 | FStar_Parser_AST.Ensures uu____16784 -> true
                 | uu____16793 -> false)
             in
          let is_app head uu____16811 =
            match uu____16811 with
            | (t1,uu____16819) ->
                let uu____16820 =
                  let uu____16821 = unparen t1  in
                  uu____16821.FStar_Parser_AST.tm  in
                (match uu____16820 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16824;
                        FStar_Parser_AST.level = uu____16825;_},uu____16826,uu____16827)
                     ->
                     let uu____16828 =
                       let uu____16830 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16830  in
                     uu____16828 = head
                 | uu____16832 -> false)
             in
          let is_smt_pat uu____16844 =
            match uu____16844 with
            | (t1,uu____16851) ->
                let uu____16852 =
                  let uu____16853 = unparen t1  in
                  uu____16853.FStar_Parser_AST.tm  in
                (match uu____16852 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16857);
                              FStar_Parser_AST.range = uu____16858;
                              FStar_Parser_AST.level = uu____16859;_},uu____16860)::uu____16861::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16901 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16901 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16913;
                              FStar_Parser_AST.level = uu____16914;_},uu____16915)::uu____16916::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16944 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16944 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16952 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16987 = head_and_args t1  in
            match uu____16987 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17045 =
                       let uu____17047 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17047  in
                     uu____17045 = "Lemma" ->
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
                     let thunk_ens uu____17083 =
                       match uu____17083 with
                       | (e,i) ->
                           let uu____17094 = FStar_Parser_AST.thunk e  in
                           (uu____17094, i)
                        in
                     let fail_lemma uu____17106 =
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
                           let uu____17212 =
                             let uu____17219 =
                               let uu____17226 = thunk_ens ens  in
                               [uu____17226; nil_pat]  in
                             req_true :: uu____17219  in
                           unit_tm :: uu____17212
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17273 =
                             let uu____17280 =
                               let uu____17287 = thunk_ens ens  in
                               [uu____17287; nil_pat]  in
                             req :: uu____17280  in
                           unit_tm :: uu____17273
                       | ens::smtpat::[] when
                           (((let uu____17336 = is_requires ens  in
                              Prims.op_Negation uu____17336) &&
                               (let uu____17339 = is_smt_pat ens  in
                                Prims.op_Negation uu____17339))
                              &&
                              (let uu____17342 = is_decreases ens  in
                               Prims.op_Negation uu____17342))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17344 =
                             let uu____17351 =
                               let uu____17358 = thunk_ens ens  in
                               [uu____17358; smtpat]  in
                             req_true :: uu____17351  in
                           unit_tm :: uu____17344
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17405 =
                             let uu____17412 =
                               let uu____17419 = thunk_ens ens  in
                               [uu____17419; nil_pat; dec]  in
                             req_true :: uu____17412  in
                           unit_tm :: uu____17405
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17479 =
                             let uu____17486 =
                               let uu____17493 = thunk_ens ens  in
                               [uu____17493; smtpat; dec]  in
                             req_true :: uu____17486  in
                           unit_tm :: uu____17479
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17553 =
                             let uu____17560 =
                               let uu____17567 = thunk_ens ens  in
                               [uu____17567; nil_pat; dec]  in
                             req :: uu____17560  in
                           unit_tm :: uu____17553
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17627 =
                             let uu____17634 =
                               let uu____17641 = thunk_ens ens  in
                               [uu____17641; smtpat]  in
                             req :: uu____17634  in
                           unit_tm :: uu____17627
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17706 =
                             let uu____17713 =
                               let uu____17720 = thunk_ens ens  in
                               [uu____17720; dec; smtpat]  in
                             req :: uu____17713  in
                           unit_tm :: uu____17706
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17782 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17782, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17810 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17810
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17812 =
                          let uu____17814 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17814  in
                        uu____17812 = "Tot")
                     ->
                     let uu____17817 =
                       let uu____17824 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17824, [])  in
                     (uu____17817, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17842 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17842
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17844 =
                          let uu____17846 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17846  in
                        uu____17844 = "GTot")
                     ->
                     let uu____17849 =
                       let uu____17856 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17856, [])  in
                     (uu____17849, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17874 =
                         let uu____17876 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17876  in
                       uu____17874 = "Type") ||
                        (let uu____17880 =
                           let uu____17882 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17882  in
                         uu____17880 = "Type0"))
                       ||
                       (let uu____17886 =
                          let uu____17888 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17888  in
                        uu____17886 = "Effect")
                     ->
                     let uu____17891 =
                       let uu____17898 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17898, [])  in
                     (uu____17891, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17921 when allow_type_promotion ->
                     let default_effect =
                       let uu____17923 = FStar_Options.ml_ish ()  in
                       if uu____17923
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17929 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17929
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17936 =
                       let uu____17943 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17943, [])  in
                     (uu____17936, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17966 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17985 = pre_process_comp_typ t  in
          match uu____17985 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18037 =
                    let uu____18043 =
                      let uu____18045 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18045
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18043)
                     in
                  fail uu____18037)
               else ();
               (let is_universe uu____18061 =
                  match uu____18061 with
                  | (uu____18067,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18069 = FStar_Util.take is_universe args  in
                match uu____18069 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18128  ->
                           match uu____18128 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18135 =
                      let uu____18150 = FStar_List.hd args1  in
                      let uu____18159 = FStar_List.tl args1  in
                      (uu____18150, uu____18159)  in
                    (match uu____18135 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18214 =
                           let is_decrease uu____18253 =
                             match uu____18253 with
                             | (t1,uu____18264) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18275;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18276;_},uu____18277::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18316 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18214 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18433  ->
                                        match uu____18433 with
                                        | (t1,uu____18443) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18452,(arg,uu____18454)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18493 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18514 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18526 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18526
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18533 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18533
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18543 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18543
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18550 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18550
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18557 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18557
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18564 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18564
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18585 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18585
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
                                                    let uu____18676 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18676
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
                                              | uu____18697 -> pat  in
                                            let uu____18698 =
                                              let uu____18709 =
                                                let uu____18720 =
                                                  let uu____18729 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18729, aq)  in
                                                [uu____18720]  in
                                              ens :: uu____18709  in
                                            req :: uu____18698
                                        | uu____18770 -> rest2
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
        let uu___2414_18805 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2414_18805.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2414_18805.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2421_18859 = b  in
             {
               FStar_Parser_AST.b = (uu___2421_18859.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2421_18859.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2421_18859.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18888 body1 =
          match uu____18888 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18934::uu____18935) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18953 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2440_18981 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18982 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2440_18981.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18982;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2440_18981.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19045 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19045))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19076 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19076 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2453_19086 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2453_19086.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2453_19086.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19092 =
                     let uu____19095 =
                       let uu____19096 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19096]  in
                     no_annot_abs uu____19095 body2  in
                   FStar_All.pipe_left setpos uu____19092  in
                 let uu____19117 =
                   let uu____19118 =
                     let uu____19135 =
                       let uu____19138 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19138
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19140 =
                       let uu____19151 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19151]  in
                     (uu____19135, uu____19140)  in
                   FStar_Syntax_Syntax.Tm_app uu____19118  in
                 FStar_All.pipe_left mk uu____19117)
        | uu____19190 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19255 = q (rest, pats, body)  in
              let uu____19258 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19255 uu____19258
                FStar_Parser_AST.Formula
               in
            let uu____19259 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19259 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19270 -> failwith "impossible"  in
      let uu____19274 =
        let uu____19275 = unparen f  in uu____19275.FStar_Parser_AST.tm  in
      match uu____19274 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19288,uu____19289) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19313,uu____19314) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19370 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19370
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19414 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19414
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19478 -> desugar_term env f

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
          let uu____19489 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19489)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19494 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19494)
      | FStar_Parser_AST.TVariable x ->
          let uu____19498 =
            let uu____19499 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19499
             in
          ((FStar_Pervasives_Native.Some x), uu____19498)
      | FStar_Parser_AST.NoName t ->
          let uu____19503 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19503)
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
      fun uu___11_19511  ->
        match uu___11_19511 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19533 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19533, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19550 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19550 with
             | (env1,a1) ->
                 let uu____19567 =
                   let uu____19574 = trans_aqual env1 imp  in
                   ((let uu___2553_19580 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2553_19580.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2553_19580.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19574)
                    in
                 (uu____19567, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19588  ->
      match uu___12_19588 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19592 =
            let uu____19593 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19593  in
          FStar_Pervasives_Native.Some uu____19592
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19621 =
        FStar_List.fold_left
          (fun uu____19654  ->
             fun b  ->
               match uu____19654 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2571_19698 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2571_19698.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2571_19698.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2571_19698.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19713 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19713 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2581_19731 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2581_19731.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2581_19731.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19732 =
                               let uu____19739 =
                                 let uu____19744 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19744)  in
                               uu____19739 :: out  in
                             (env2, uu____19732))
                    | uu____19755 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19621 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19843 =
          let uu____19844 = unparen t  in uu____19844.FStar_Parser_AST.tm  in
        match uu____19843 with
        | FStar_Parser_AST.Var lid when
            let uu____19846 = FStar_Ident.string_of_lid lid  in
            uu____19846 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19850 ->
            let uu____19851 =
              let uu____19857 =
                let uu____19859 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19859  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19857)  in
            FStar_Errors.raise_error uu____19851 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19876) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19878) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19881 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19899 = binder_ident b  in
         FStar_Common.list_of_option uu____19899) bs
  
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
               (fun uu___13_19936  ->
                  match uu___13_19936 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19941 -> false))
           in
        let quals2 q =
          let uu____19955 =
            (let uu____19959 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19959) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19955
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19976 = FStar_Ident.range_of_lid disc_name  in
                let uu____19977 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19976;
                  FStar_Syntax_Syntax.sigquals = uu____19977;
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
            let uu____20017 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20053  ->
                        match uu____20053 with
                        | (x,uu____20064) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20074 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20074)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20076 =
                                   let uu____20078 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20078  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20076)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20096 =
                                  FStar_List.filter
                                    (fun uu___14_20100  ->
                                       match uu___14_20100 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20103 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20096
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20118  ->
                                        match uu___15_20118 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20123 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20126 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20126;
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
                                 let uu____20133 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20133
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20144 =
                                   let uu____20149 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20149  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20144;
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
                                 let uu____20153 =
                                   let uu____20154 =
                                     let uu____20161 =
                                       let uu____20164 =
                                         let uu____20165 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20165
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20164]  in
                                     ((false, [lb]), uu____20161)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20154
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20153;
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
            FStar_All.pipe_right uu____20017 FStar_List.flatten
  
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
            (lid,uu____20214,t,uu____20216,n,uu____20218) when
            let uu____20225 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20225 ->
            let uu____20227 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20227 with
             | (formals,uu____20237) ->
                 (match formals with
                  | [] -> []
                  | uu____20250 ->
                      let filter_records uu___16_20258 =
                        match uu___16_20258 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20261,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20273 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20275 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20275 with
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
                      let uu____20287 = FStar_Util.first_N n formals  in
                      (match uu____20287 with
                       | (uu____20316,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20350 -> []
  
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
                        let uu____20444 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20444
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20468 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20468
                        then
                          let uu____20474 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20474
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20478 =
                          let uu____20483 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20483  in
                        let uu____20484 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20490 =
                              let uu____20493 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20493  in
                            FStar_Syntax_Util.arrow typars uu____20490
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20498 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20478;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20484;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20498;
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
          let tycon_id uu___17_20552 =
            match uu___17_20552 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20554,uu____20555) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20565,uu____20566,uu____20567) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20577,uu____20578,uu____20579) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20601,uu____20602,uu____20603) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20641) ->
                let uu____20642 =
                  let uu____20643 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20643  in
                let uu____20644 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20642 uu____20644
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20646 =
                  let uu____20647 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20647  in
                let uu____20648 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20646 uu____20648
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20650) ->
                let uu____20651 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20651 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20653 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20653 FStar_Parser_AST.Type_level
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
              | uu____20683 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20691 =
                     let uu____20692 =
                       let uu____20699 = binder_to_term b  in
                       (out, uu____20699, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20692  in
                   FStar_Parser_AST.mk_term uu____20691
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20711 =
            match uu___18_20711 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20743 =
                    let uu____20749 =
                      let uu____20751 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20751  in
                    let uu____20754 = FStar_Ident.range_of_id id  in
                    (uu____20749, uu____20754)  in
                  FStar_Ident.mk_ident uu____20743  in
                let mfields =
                  FStar_List.map
                    (fun uu____20767  ->
                       match uu____20767 with
                       | (x,t) ->
                           let uu____20774 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20774
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20776 =
                    let uu____20777 =
                      let uu____20778 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20778  in
                    let uu____20779 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20777 uu____20779
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20776 parms  in
                let constrTyp =
                  let uu____20781 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20781 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20787 = binder_idents parms  in id :: uu____20787
                   in
                (FStar_List.iter
                   (fun uu____20801  ->
                      match uu____20801 with
                      | (f,uu____20807) ->
                          let uu____20808 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20808
                          then
                            let uu____20813 =
                              let uu____20819 =
                                let uu____20821 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20821
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20819)
                               in
                            let uu____20825 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20813 uu____20825
                          else ()) fields;
                 (let uu____20828 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20828)))
            | uu____20882 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20922 =
            match uu___19_20922 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20946 = typars_of_binders _env binders  in
                (match uu____20946 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20982 =
                         let uu____20983 =
                           let uu____20984 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20984  in
                         let uu____20985 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20983 uu____20985
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20982 binders  in
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
                     let uu____20994 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20994 with
                      | (_env1,uu____21011) ->
                          let uu____21018 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21018 with
                           | (_env2,uu____21035) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21042 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21085 =
              FStar_List.fold_left
                (fun uu____21119  ->
                   fun uu____21120  ->
                     match (uu____21119, uu____21120) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21189 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21189 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21085 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21280 =
                      let uu____21281 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21281  in
                    FStar_Pervasives_Native.Some uu____21280
                | uu____21282 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21290 = desugar_abstract_tc quals env [] tc  in
              (match uu____21290 with
               | (uu____21303,uu____21304,se,uu____21306) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21309,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21328 =
                                 let uu____21330 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21330  in
                               if uu____21328
                               then
                                 let uu____21333 =
                                   let uu____21339 =
                                     let uu____21341 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21341
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21339)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21333
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
                           | uu____21354 ->
                               let uu____21355 =
                                 let uu____21362 =
                                   let uu____21363 =
                                     let uu____21378 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21378)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21363
                                    in
                                 FStar_Syntax_Syntax.mk uu____21362  in
                               uu____21355 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2858_21391 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2858_21391.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2858_21391.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2858_21391.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2858_21391.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21392 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21407 = typars_of_binders env binders  in
              (match uu____21407 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21441 =
                           FStar_Util.for_some
                             (fun uu___20_21444  ->
                                match uu___20_21444 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21447 -> false) quals
                            in
                         if uu____21441
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21455 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21455
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21460 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21466  ->
                               match uu___21_21466 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21469 -> false))
                        in
                     if uu____21460
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21483 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21483
                     then
                       let uu____21489 =
                         let uu____21496 =
                           let uu____21497 = unparen t  in
                           uu____21497.FStar_Parser_AST.tm  in
                         match uu____21496 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21518 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21548)::args_rev ->
                                   let uu____21560 =
                                     let uu____21561 = unparen last_arg  in
                                     uu____21561.FStar_Parser_AST.tm  in
                                   (match uu____21560 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21589 -> ([], args))
                               | uu____21598 -> ([], args)  in
                             (match uu____21518 with
                              | (cattributes,args1) ->
                                  let uu____21637 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21637))
                         | uu____21648 -> (t, [])  in
                       match uu____21489 with
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
                                  (fun uu___22_21671  ->
                                     match uu___22_21671 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21674 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21682)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21702 = tycon_record_as_variant trec  in
              (match uu____21702 with
               | (t,fs) ->
                   let uu____21719 =
                     let uu____21722 =
                       let uu____21723 =
                         let uu____21732 =
                           let uu____21735 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21735  in
                         (uu____21732, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21723  in
                     uu____21722 :: quals  in
                   desugar_tycon env d uu____21719 [t])
          | uu____21740::uu____21741 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21899 = et  in
                match uu____21899 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22109 ->
                         let trec = tc  in
                         let uu____22129 = tycon_record_as_variant trec  in
                         (match uu____22129 with
                          | (t,fs) ->
                              let uu____22185 =
                                let uu____22188 =
                                  let uu____22189 =
                                    let uu____22198 =
                                      let uu____22201 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22201  in
                                    (uu____22198, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22189
                                   in
                                uu____22188 :: quals1  in
                              collect_tcs uu____22185 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22279 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22279 with
                          | (env2,uu____22336,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22473 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22473 with
                          | (env2,uu____22530,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22646 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22692 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22692 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23144  ->
                             match uu___24_23144 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23198,uu____23199);
                                    FStar_Syntax_Syntax.sigrng = uu____23200;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23201;
                                    FStar_Syntax_Syntax.sigmeta = uu____23202;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23203;
                                    FStar_Syntax_Syntax.sigopts = uu____23204;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23266 =
                                     typars_of_binders env1 binders  in
                                   match uu____23266 with
                                   | (env2,tpars1) ->
                                       let uu____23293 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23293 with
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
                                 let uu____23322 =
                                   let uu____23333 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23333)  in
                                 [uu____23322]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23369);
                                    FStar_Syntax_Syntax.sigrng = uu____23370;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23372;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23373;
                                    FStar_Syntax_Syntax.sigopts = uu____23374;_},constrs,tconstr,quals1)
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
                                 let uu____23465 = push_tparams env1 tpars
                                    in
                                 (match uu____23465 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23524  ->
                                             match uu____23524 with
                                             | (x,uu____23536) ->
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
                                        let uu____23547 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23547
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23570 =
                                        let uu____23589 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23666  ->
                                                  match uu____23666 with
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
                                                        let uu____23709 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23709
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
                                                                uu___23_23720
                                                                 ->
                                                                match uu___23_23720
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23732
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23740 =
                                                        let uu____23751 =
                                                          let uu____23752 =
                                                            let uu____23753 =
                                                              let uu____23769
                                                                =
                                                                let uu____23770
                                                                  =
                                                                  let uu____23773
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23773
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23770
                                                                 in
                                                              (name, univs,
                                                                uu____23769,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23753
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23752;
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
                                                        (tps, uu____23751)
                                                         in
                                                      (name, uu____23740)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23589
                                         in
                                      (match uu____23570 with
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
                             | uu____23905 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23986  ->
                             match uu____23986 with | (uu____23997,se) -> se))
                      in
                   let uu____24011 =
                     let uu____24018 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24018 rng
                      in
                   (match uu____24011 with
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
                               (fun uu____24063  ->
                                  match uu____24063 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24111,tps,k,uu____24114,constrs)
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
                                      let uu____24135 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24150 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24167,uu____24168,uu____24169,uu____24170,uu____24171)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24178
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24150
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24182 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24189  ->
                                                          match uu___25_24189
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24191 ->
                                                              true
                                                          | uu____24201 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24182))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24135
                                  | uu____24203 -> []))
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
      let uu____24240 =
        FStar_List.fold_left
          (fun uu____24275  ->
             fun b  ->
               match uu____24275 with
               | (env1,binders1) ->
                   let uu____24319 = desugar_binder env1 b  in
                   (match uu____24319 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24342 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24342 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24395 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24240 with
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
          let uu____24499 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24506  ->
                    match uu___26_24506 with
                    | FStar_Syntax_Syntax.Reflectable uu____24508 -> true
                    | uu____24510 -> false))
             in
          if uu____24499
          then
            let monad_env =
              let uu____24514 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24514  in
            let reflect_lid =
              let uu____24516 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24516
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
        let warn1 uu____24567 =
          if warn
          then
            let uu____24569 =
              let uu____24575 =
                let uu____24577 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24577
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24575)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24569
          else ()  in
        let uu____24583 = FStar_Syntax_Util.head_and_args at  in
        match uu____24583 with
        | (hd,args) ->
            let uu____24636 =
              let uu____24637 = FStar_Syntax_Subst.compress hd  in
              uu____24637.FStar_Syntax_Syntax.n  in
            (match uu____24636 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24681)::[] ->
                      let uu____24706 =
                        let uu____24711 =
                          let uu____24720 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24720 a1  in
                        uu____24711 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24706 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24743 =
                             let uu____24749 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24749  in
                           (uu____24743, true)
                       | uu____24764 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24780 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24802 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24919 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24919 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24968 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24968 with | (res1,uu____24990) -> rebind res1 true)
  
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
        | uu____25317 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25375 = get_fail_attr1 warn at  in
             comb uu____25375 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25410 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25410 with
        | FStar_Pervasives_Native.None  ->
            let uu____25413 =
              let uu____25419 =
                let uu____25421 =
                  let uu____25423 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25423 " not found"  in
                Prims.op_Hat "Effect name " uu____25421  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25419)  in
            FStar_Errors.raise_error uu____25413 r
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
                    let uu____25579 = desugar_binders monad_env eff_binders
                       in
                    match uu____25579 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25618 =
                            let uu____25627 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25627  in
                          FStar_List.length uu____25618  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25645 =
                              let uu____25651 =
                                let uu____25653 =
                                  let uu____25655 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25655
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25653  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25651)
                               in
                            FStar_Errors.raise_error uu____25645
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
                                (uu____25723,uu____25724,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25726,uu____25727,uu____25728))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25743 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25746 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25758 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25758 mandatory_members)
                              eff_decls
                             in
                          match uu____25746 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25777 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25806  ->
                                        fun decl  ->
                                          match uu____25806 with
                                          | (env2,out) ->
                                              let uu____25826 =
                                                desugar_decl env2 decl  in
                                              (match uu____25826 with
                                               | (env3,ses) ->
                                                   let uu____25839 =
                                                     let uu____25842 =
                                                       FStar_List.hd ses  in
                                                     uu____25842 :: out  in
                                                   (env3, uu____25839)))
                                     (env1, []))
                                 in
                              (match uu____25777 with
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
                                                 (uu____25888,uu____25889,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25892,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25893,(def,uu____25895)::
                                                        (cps_type,uu____25897)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25898;
                                                     FStar_Parser_AST.level =
                                                       uu____25899;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25932 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25932 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25964 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25965 =
                                                        let uu____25966 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25966
                                                         in
                                                      let uu____25973 =
                                                        let uu____25974 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25974
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25964;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25965;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25973
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25981,uu____25982,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25985,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26001 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26001 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26033 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26034 =
                                                        let uu____26035 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26035
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26033;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26034;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26042 ->
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
                                       let uu____26061 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26061
                                        in
                                     let uu____26063 =
                                       let uu____26064 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26064
                                        in
                                     ([], uu____26063)  in
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
                                       let uu____26086 =
                                         let uu____26087 =
                                           let uu____26090 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26090
                                            in
                                         let uu____26092 =
                                           let uu____26095 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26095
                                            in
                                         let uu____26097 =
                                           let uu____26100 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26100
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
                                             uu____26087;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26092;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26097
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26086
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26134 =
                                            match uu____26134 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26181 =
                                            let uu____26182 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26184 =
                                              let uu____26189 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26189 to_comb
                                               in
                                            let uu____26207 =
                                              let uu____26212 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26212 to_comb
                                               in
                                            let uu____26230 =
                                              let uu____26235 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26235 to_comb
                                               in
                                            let uu____26253 =
                                              let uu____26258 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26258 to_comb
                                               in
                                            let uu____26276 =
                                              let uu____26281 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26281 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26182;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26184;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26207;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26230;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26253;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26276
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26181)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26304  ->
                                                 match uu___27_26304 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26307 -> true
                                                 | uu____26309 -> false)
                                              qualifiers
                                             in
                                          let uu____26311 =
                                            let uu____26312 =
                                              lookup "return_wp"  in
                                            let uu____26314 =
                                              lookup "bind_wp"  in
                                            let uu____26316 =
                                              lookup "stronger"  in
                                            let uu____26318 =
                                              lookup "if_then_else"  in
                                            let uu____26320 = lookup "ite_wp"
                                               in
                                            let uu____26322 =
                                              lookup "close_wp"  in
                                            let uu____26324 =
                                              lookup "trivial"  in
                                            let uu____26326 =
                                              if rr
                                              then
                                                let uu____26332 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26332
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26336 =
                                              if rr
                                              then
                                                let uu____26342 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26342
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26346 =
                                              if rr
                                              then
                                                let uu____26352 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26352
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26312;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26314;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26316;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26318;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26320;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26322;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26324;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26326;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26336;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26346
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26311)
                                      in
                                   let sigel =
                                     let uu____26357 =
                                       let uu____26358 =
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
                                           uu____26358
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26357
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
                                               let uu____26375 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26375) env3)
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
                let uu____26398 = desugar_binders env1 eff_binders  in
                match uu____26398 with
                | (env2,binders) ->
                    let uu____26435 =
                      let uu____26446 = head_and_args defn  in
                      match uu____26446 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26483 ->
                                let uu____26484 =
                                  let uu____26490 =
                                    let uu____26492 =
                                      let uu____26494 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26494 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26492  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26490)
                                   in
                                FStar_Errors.raise_error uu____26484
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26500 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26530)::args_rev ->
                                let uu____26542 =
                                  let uu____26543 = unparen last_arg  in
                                  uu____26543.FStar_Parser_AST.tm  in
                                (match uu____26542 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26571 -> ([], args))
                            | uu____26580 -> ([], args)  in
                          (match uu____26500 with
                           | (cattributes,args1) ->
                               let uu____26623 = desugar_args env2 args1  in
                               let uu____26624 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26623, uu____26624))
                       in
                    (match uu____26435 with
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
                          (let uu____26664 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26664 with
                           | (ed_binders,uu____26678,ed_binders_opening) ->
                               let sub' shift_n uu____26697 =
                                 match uu____26697 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26712 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26712 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26716 =
                                       let uu____26717 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26717)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26716
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26738 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26739 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26740 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26756 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26757 =
                                          let uu____26758 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26758
                                           in
                                        let uu____26773 =
                                          let uu____26774 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26774
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26756;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26757;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26773
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
                                     uu____26738;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26739;
                                   FStar_Syntax_Syntax.actions = uu____26740;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26790 =
                                   let uu____26793 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26793 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26790;
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
                                           let uu____26808 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26808) env3)
                                  in
                               let env5 =
                                 let uu____26810 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26810
                                 then
                                   let reflect_lid =
                                     let uu____26817 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26817
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
             let uu____26850 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26850) ats
         in
      let env0 =
        let uu____26871 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26871 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26886 =
        let uu____26893 = get_fail_attr false attrs  in
        match uu____26893 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3413_26930 = d  in
              {
                FStar_Parser_AST.d = (uu___3413_26930.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3413_26930.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3413_26930.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26931 =
              FStar_Errors.catch_errors
                (fun uu____26949  ->
                   FStar_Options.with_saved_options
                     (fun uu____26955  -> desugar_decl_noattrs env d1))
               in
            (match uu____26931 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3428_27015 = se  in
                             let uu____27016 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3428_27015.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3428_27015.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3428_27015.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3428_27015.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27016;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3428_27015.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____27069 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27069 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27118 =
                                 let uu____27124 =
                                   let uu____27126 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27129 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27132 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27134 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27136 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27126 uu____27129 uu____27132
                                     uu____27134 uu____27136
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27124)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27118);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26886 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27174;
                FStar_Syntax_Syntax.sigrng = uu____27175;
                FStar_Syntax_Syntax.sigquals = uu____27176;
                FStar_Syntax_Syntax.sigmeta = uu____27177;
                FStar_Syntax_Syntax.sigattrs = uu____27178;
                FStar_Syntax_Syntax.sigopts = uu____27179;_}::[] ->
                let uu____27192 =
                  let uu____27195 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27195  in
                FStar_All.pipe_right uu____27192
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27203 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27203))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27216;
                FStar_Syntax_Syntax.sigrng = uu____27217;
                FStar_Syntax_Syntax.sigquals = uu____27218;
                FStar_Syntax_Syntax.sigmeta = uu____27219;
                FStar_Syntax_Syntax.sigattrs = uu____27220;
                FStar_Syntax_Syntax.sigopts = uu____27221;_}::uu____27222 ->
                let uu____27247 =
                  let uu____27250 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27250  in
                FStar_All.pipe_right uu____27247
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27258 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27258))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27274;
                FStar_Syntax_Syntax.sigquals = uu____27275;
                FStar_Syntax_Syntax.sigmeta = uu____27276;
                FStar_Syntax_Syntax.sigattrs = uu____27277;
                FStar_Syntax_Syntax.sigopts = uu____27278;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27299 -> []  in
          let attrs1 =
            let uu____27305 = val_attrs sigelts  in
            FStar_List.append attrs uu____27305  in
          let uu____27308 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3488_27312 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3488_27312.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3488_27312.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3488_27312.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3488_27312.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3488_27312.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27308)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27319 = desugar_decl_aux env d  in
      match uu____27319 with
      | (env1,ses) ->
          let uu____27330 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27330)

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
          let uu____27362 = FStar_Syntax_DsEnv.iface env  in
          if uu____27362
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27377 =
               let uu____27379 =
                 let uu____27381 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27382 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27381
                   uu____27382
                  in
               Prims.op_Negation uu____27379  in
             if uu____27377
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27396 =
                  let uu____27398 =
                    let uu____27400 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27400 lid  in
                  Prims.op_Negation uu____27398  in
                if uu____27396
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27414 =
                     let uu____27416 =
                       let uu____27418 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27418
                         lid
                        in
                     Prims.op_Negation uu____27416  in
                   if uu____27414
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27436 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27436, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27465)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27484 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27493 =
            let uu____27498 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27498 tcs  in
          (match uu____27493 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27515 =
                   let uu____27516 =
                     let uu____27523 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27523  in
                   [uu____27516]  in
                 let uu____27536 =
                   let uu____27539 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27542 =
                     let uu____27553 =
                       let uu____27562 =
                         let uu____27563 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27563  in
                       FStar_Syntax_Syntax.as_arg uu____27562  in
                     [uu____27553]  in
                   FStar_Syntax_Util.mk_app uu____27539 uu____27542  in
                 FStar_Syntax_Util.abs uu____27515 uu____27536
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27603,id))::uu____27605 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27608::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27612 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27612 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27618 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27618]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27639) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27649,uu____27650,uu____27651,uu____27652,uu____27653)
                     ->
                     let uu____27662 =
                       let uu____27663 =
                         let uu____27664 =
                           let uu____27671 = mkclass lid  in
                           (meths, uu____27671)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27664  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27663;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27662]
                 | uu____27674 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27708;
                    FStar_Parser_AST.prange = uu____27709;_},uu____27710)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27720;
                    FStar_Parser_AST.prange = uu____27721;_},uu____27722)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27738;
                         FStar_Parser_AST.prange = uu____27739;_},uu____27740);
                    FStar_Parser_AST.prange = uu____27741;_},uu____27742)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27764;
                         FStar_Parser_AST.prange = uu____27765;_},uu____27766);
                    FStar_Parser_AST.prange = uu____27767;_},uu____27768)::[]
                   -> false
               | (p,uu____27797)::[] ->
                   let uu____27806 = is_app_pattern p  in
                   Prims.op_Negation uu____27806
               | uu____27808 -> false)
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
            let uu____27883 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27883 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27896 =
                     let uu____27897 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27897.FStar_Syntax_Syntax.n  in
                   match uu____27896 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27907) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27938 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27963  ->
                                match uu____27963 with
                                | (qs,ats) ->
                                    let uu____27990 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27990 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27938 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28044::uu____28045 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28048 -> val_quals  in
                            let quals2 =
                              let uu____28052 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28085  ->
                                        match uu____28085 with
                                        | (uu____28099,(uu____28100,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28052
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28120 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28120
                              then
                                let uu____28126 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3665_28141 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3667_28143 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3667_28143.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3667_28143.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3665_28141.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28126)
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
                   | uu____28168 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28176 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28195 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28176 with
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
                       let uu___3690_28232 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3690_28232.FStar_Parser_AST.prange)
                       }
                   | uu____28239 -> var_pat  in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals)
                      in
                   desugar_decl env
                     (let uu___3696_28250 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3696_28250.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3696_28250.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28266 =
                     let uu____28267 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28267  in
                   FStar_Parser_AST.mk_term uu____28266
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28291 id_opt =
                   match uu____28291 with
                   | (env1,ses) ->
                       let uu____28313 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28325 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28325
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28327 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28327
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
                               let uu____28333 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28333
                                in
                             let bv_pat1 =
                               let uu____28337 =
                                 let uu____28338 =
                                   let uu____28349 =
                                     let uu____28356 =
                                       let uu____28357 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28357  in
                                     (uu____28356,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28349)  in
                                 FStar_Parser_AST.PatAscribed uu____28338  in
                               let uu____28366 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28337
                                 uu____28366
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28313 with
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
                            let id_decl1 =
                              let uu___3720_28420 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3720_28420.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3720_28420.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3720_28420.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28421 = desugar_decl env1 id_decl1  in
                            (match uu____28421 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28457 id =
                   match uu____28457 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28496 =
                   match uu____28496 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28520 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28520 FStar_Util.set_elements
                    in
                 let uu____28527 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28530 = is_var_pattern pat  in
                      Prims.op_Negation uu____28530)
                    in
                 if uu____28527
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
            let uu____28556 = close_fun env t  in
            desugar_term env uu____28556  in
          let quals1 =
            let uu____28560 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28560
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28572 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28572;
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
                let uu____28585 =
                  let uu____28594 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28594]  in
                let uu____28613 =
                  let uu____28616 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28616
                   in
                FStar_Syntax_Util.arrow uu____28585 uu____28613
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
          uu____28679) ->
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
          let uu____28696 =
            let uu____28698 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28698  in
          if uu____28696
          then
            let uu____28705 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28723 =
                    let uu____28726 =
                      let uu____28727 = desugar_term env t  in
                      ([], uu____28727)  in
                    FStar_Pervasives_Native.Some uu____28726  in
                  (uu____28723, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28740 =
                    let uu____28743 =
                      let uu____28744 = desugar_term env wp  in
                      ([], uu____28744)  in
                    FStar_Pervasives_Native.Some uu____28743  in
                  let uu____28751 =
                    let uu____28754 =
                      let uu____28755 = desugar_term env t  in
                      ([], uu____28755)  in
                    FStar_Pervasives_Native.Some uu____28754  in
                  (uu____28740, uu____28751)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28767 =
                    let uu____28770 =
                      let uu____28771 = desugar_term env t  in
                      ([], uu____28771)  in
                    FStar_Pervasives_Native.Some uu____28770  in
                  (FStar_Pervasives_Native.None, uu____28767)
               in
            (match uu____28705 with
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
                   let uu____28805 =
                     let uu____28808 =
                       let uu____28809 = desugar_term env t  in
                       ([], uu____28809)  in
                     FStar_Pervasives_Native.Some uu____28808  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28805
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
             | uu____28816 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28829 =
            let uu____28830 =
              let uu____28831 =
                let uu____28832 =
                  let uu____28843 =
                    let uu____28844 = desugar_term env bind  in
                    ([], uu____28844)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28843,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28832  in
              {
                FStar_Syntax_Syntax.sigel = uu____28831;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28830]  in
          (env, uu____28829)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28863 =
              let uu____28864 =
                let uu____28871 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28871, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28864  in
            {
              FStar_Syntax_Syntax.sigel = uu____28863;
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
      let uu____28898 =
        FStar_List.fold_left
          (fun uu____28918  ->
             fun d  ->
               match uu____28918 with
               | (env1,sigelts) ->
                   let uu____28938 = desugar_decl env1 d  in
                   (match uu____28938 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28898 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29029) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29033;
               FStar_Syntax_Syntax.exports = uu____29034;
               FStar_Syntax_Syntax.is_interface = uu____29035;_},FStar_Parser_AST.Module
             (current_lid,uu____29037)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29046) ->
              let uu____29049 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29049
           in
        let uu____29054 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29096 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29096, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29118 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29118, mname, decls, false)
           in
        match uu____29054 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29160 = desugar_decls env2 decls  in
            (match uu____29160 with
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
          let uu____29228 =
            (FStar_Options.interactive ()) &&
              (let uu____29231 =
                 let uu____29233 =
                   let uu____29235 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29235  in
                 FStar_Util.get_file_extension uu____29233  in
               FStar_List.mem uu____29231 ["fsti"; "fsi"])
             in
          if uu____29228 then as_interface m else m  in
        let uu____29249 = desugar_modul_common curmod env m1  in
        match uu____29249 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29271 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29271, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29293 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29293 with
      | (env1,modul,pop_when_done) ->
          let uu____29310 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29310 with
           | (env2,modul1) ->
               ((let uu____29322 =
                   let uu____29324 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29324  in
                 if uu____29322
                 then
                   let uu____29327 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29327
                 else ());
                (let uu____29332 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29332, modul1))))
  
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
        (fun uu____29382  ->
           let uu____29383 = desugar_modul env modul  in
           match uu____29383 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29421  ->
           let uu____29422 = desugar_decls env decls  in
           match uu____29422 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29473  ->
             let uu____29474 = desugar_partial_modul modul env a_modul  in
             match uu____29474 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29569 ->
                  let t =
                    let uu____29579 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29579  in
                  let uu____29592 =
                    let uu____29593 = FStar_Syntax_Subst.compress t  in
                    uu____29593.FStar_Syntax_Syntax.n  in
                  (match uu____29592 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29605,uu____29606)
                       -> bs1
                   | uu____29631 -> failwith "Impossible")
               in
            let uu____29641 =
              let uu____29648 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29648
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29641 with
            | (binders,uu____29650,binders_opening) ->
                let erase_term t =
                  let uu____29658 =
                    let uu____29659 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29659  in
                  FStar_Syntax_Subst.close binders uu____29658  in
                let erase_tscheme uu____29677 =
                  match uu____29677 with
                  | (us,t) ->
                      let t1 =
                        let uu____29697 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29697 t  in
                      let uu____29700 =
                        let uu____29701 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29701  in
                      ([], uu____29700)
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
                    | uu____29724 ->
                        let bs =
                          let uu____29734 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29734  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29774 =
                          let uu____29775 =
                            let uu____29778 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29778  in
                          uu____29775.FStar_Syntax_Syntax.n  in
                        (match uu____29774 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29780,uu____29781) -> bs1
                         | uu____29806 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29814 =
                      let uu____29815 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29815  in
                    FStar_Syntax_Subst.close binders uu____29814  in
                  let uu___3995_29816 = action  in
                  let uu____29817 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29818 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3995_29816.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3995_29816.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29817;
                    FStar_Syntax_Syntax.action_typ = uu____29818
                  }  in
                let uu___3997_29819 = ed  in
                let uu____29820 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29821 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29822 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29823 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3997_29819.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3997_29819.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29820;
                  FStar_Syntax_Syntax.signature = uu____29821;
                  FStar_Syntax_Syntax.combinators = uu____29822;
                  FStar_Syntax_Syntax.actions = uu____29823;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3997_29819.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4004_29839 = se  in
                  let uu____29840 =
                    let uu____29841 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29841  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29840;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4004_29839.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4004_29839.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4004_29839.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4004_29839.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4004_29839.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29843 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29844 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29844 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29861 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29861
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29863 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29863)
  