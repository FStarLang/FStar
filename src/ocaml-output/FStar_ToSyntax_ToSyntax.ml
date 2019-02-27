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
             (fun uu____57565  ->
                match uu____57565 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57620  ->
                             match uu____57620 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57638 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57638 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57644 =
                                     let uu____57645 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57645]  in
                                   FStar_Syntax_Subst.close uu____57644
                                     branch1
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
      fun uu___429_57702  ->
        match uu___429_57702 with
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
  fun uu___430_57722  ->
    match uu___430_57722 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___431_57740  ->
    match uu___431_57740 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57743 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57751 .
    FStar_Parser_AST.imp ->
      'Auu____57751 ->
        ('Auu____57751 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57777 .
    FStar_Parser_AST.imp ->
      'Auu____57777 ->
        ('Auu____57777 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57796 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57817 -> true
            | uu____57823 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57832 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57839 =
      let uu____57840 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57840  in
    FStar_Parser_AST.mk_term uu____57839 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57850 =
      let uu____57851 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57851  in
    FStar_Parser_AST.mk_term uu____57850 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57867 =
        let uu____57868 = unparen t  in uu____57868.FStar_Parser_AST.tm  in
      match uu____57867 with
      | FStar_Parser_AST.Name l ->
          let uu____57871 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57871 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57878) ->
          let uu____57891 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57891 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57898,uu____57899) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57904,uu____57905) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57910,t1) -> is_comp_type env t1
      | uu____57912 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____58013;
                            FStar_Syntax_Syntax.vars = uu____58014;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58042 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58042 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____58058 =
                               let uu____58059 =
                                 let uu____58062 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____58062  in
                               uu____58059.FStar_Syntax_Syntax.n  in
                             match uu____58058 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58085))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58092 -> msg
                           else msg  in
                         let uu____58095 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58095
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58100 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58100 " is deprecated"  in
                         let uu____58103 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58103
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58105 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58121 .
    'Auu____58121 ->
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
        let uu____58174 =
          let uu____58177 =
            let uu____58178 =
              let uu____58184 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58184, r)  in
            FStar_Ident.mk_ident uu____58178  in
          [uu____58177]  in
        FStar_All.pipe_right uu____58174 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58200 .
    env_t ->
      Prims.int ->
        'Auu____58200 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58238 =
              let uu____58239 =
                let uu____58240 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58240 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58239 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58238  in
          let fallback uu____58248 =
            let uu____58249 = FStar_Ident.text_of_id op  in
            match uu____58249 with
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
            | "-" when arity = (Prims.parse_int "1") ->
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
                let uu____58270 = FStar_Options.ml_ish ()  in
                if uu____58270
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
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
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | uu____58295 -> FStar_Pervasives_Native.None  in
          let uu____58297 =
            let uu____58300 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58306 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58306.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58306.FStar_Syntax_Syntax.vars)
                 }) env true uu____58300
             in
          match uu____58297 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58311 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58326 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58326
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58375 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58379 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58379 with | (env1,uu____58391) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58394,term) ->
          let uu____58396 = free_type_vars env term  in (env, uu____58396)
      | FStar_Parser_AST.TAnnotated (id1,uu____58402) ->
          let uu____58403 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58403 with | (env1,uu____58415) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58419 = free_type_vars env t  in (env, uu____58419)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58426 =
        let uu____58427 = unparen t  in uu____58427.FStar_Parser_AST.tm  in
      match uu____58426 with
      | FStar_Parser_AST.Labeled uu____58430 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58443 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58443 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58448 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58451 -> []
      | FStar_Parser_AST.Uvar uu____58452 -> []
      | FStar_Parser_AST.Var uu____58453 -> []
      | FStar_Parser_AST.Projector uu____58454 -> []
      | FStar_Parser_AST.Discrim uu____58459 -> []
      | FStar_Parser_AST.Name uu____58460 -> []
      | FStar_Parser_AST.Requires (t1,uu____58462) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58470) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58477,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58496,ts) ->
          FStar_List.collect
            (fun uu____58517  ->
               match uu____58517 with
               | (t1,uu____58525) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58526,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58534) ->
          let uu____58535 = free_type_vars env t1  in
          let uu____58538 = free_type_vars env t2  in
          FStar_List.append uu____58535 uu____58538
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58543 = free_type_vars_b env b  in
          (match uu____58543 with
           | (env1,f) ->
               let uu____58558 = free_type_vars env1 t1  in
               FStar_List.append f uu____58558)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58575 =
            FStar_List.fold_left
              (fun uu____58599  ->
                 fun bt  ->
                   match uu____58599 with
                   | (env1,free) ->
                       let uu____58623 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58638 = free_type_vars env1 body  in
                             (env1, uu____58638)
                          in
                       (match uu____58623 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58575 with
           | (env1,free) ->
               let uu____58667 = free_type_vars env1 body  in
               FStar_List.append free uu____58667)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58676 =
            FStar_List.fold_left
              (fun uu____58696  ->
                 fun binder  ->
                   match uu____58696 with
                   | (env1,free) ->
                       let uu____58716 = free_type_vars_b env1 binder  in
                       (match uu____58716 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58676 with
           | (env1,free) ->
               let uu____58747 = free_type_vars env1 body  in
               FStar_List.append free uu____58747)
      | FStar_Parser_AST.Project (t1,uu____58751) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58762 = free_type_vars env rel  in
          let uu____58765 =
            let uu____58768 = free_type_vars env init1  in
            let uu____58771 =
              FStar_List.collect
                (fun uu____58780  ->
                   match uu____58780 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58786 = free_type_vars env rel1  in
                       let uu____58789 =
                         let uu____58792 = free_type_vars env just  in
                         let uu____58795 = free_type_vars env next  in
                         FStar_List.append uu____58792 uu____58795  in
                       FStar_List.append uu____58786 uu____58789) steps
               in
            FStar_List.append uu____58768 uu____58771  in
          FStar_List.append uu____58762 uu____58765
      | FStar_Parser_AST.Abs uu____58798 -> []
      | FStar_Parser_AST.Let uu____58805 -> []
      | FStar_Parser_AST.LetOpen uu____58826 -> []
      | FStar_Parser_AST.If uu____58831 -> []
      | FStar_Parser_AST.QForall uu____58838 -> []
      | FStar_Parser_AST.QExists uu____58851 -> []
      | FStar_Parser_AST.Record uu____58864 -> []
      | FStar_Parser_AST.Match uu____58877 -> []
      | FStar_Parser_AST.TryWith uu____58892 -> []
      | FStar_Parser_AST.Bind uu____58907 -> []
      | FStar_Parser_AST.Quote uu____58914 -> []
      | FStar_Parser_AST.VQuote uu____58919 -> []
      | FStar_Parser_AST.Antiquote uu____58920 -> []
      | FStar_Parser_AST.Seq uu____58921 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58975 =
        let uu____58976 = unparen t1  in uu____58976.FStar_Parser_AST.tm  in
      match uu____58975 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____59018 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____59043 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59043  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59065 =
                     let uu____59066 =
                       let uu____59071 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59071)  in
                     FStar_Parser_AST.TAnnotated uu____59066  in
                   FStar_Parser_AST.mk_binder uu____59065
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
        let uu____59089 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59089  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59111 =
                     let uu____59112 =
                       let uu____59117 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59117)  in
                     FStar_Parser_AST.TAnnotated uu____59112  in
                   FStar_Parser_AST.mk_binder uu____59111
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59119 =
             let uu____59120 = unparen t  in uu____59120.FStar_Parser_AST.tm
              in
           match uu____59119 with
           | FStar_Parser_AST.Product uu____59121 -> t
           | uu____59128 ->
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
      | uu____59165 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59176 -> true
    | FStar_Parser_AST.PatTvar (uu____59180,uu____59181) -> true
    | FStar_Parser_AST.PatVar (uu____59187,uu____59188) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59195) -> is_var_pattern p1
    | uu____59208 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59219) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59232;
           FStar_Parser_AST.prange = uu____59233;_},uu____59234)
        -> true
    | uu____59246 -> false
  
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
    | uu____59262 -> p
  
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
            let uu____59335 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59335 with
             | (name,args,uu____59378) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59428);
               FStar_Parser_AST.prange = uu____59429;_},args)
            when is_top_level1 ->
            let uu____59439 =
              let uu____59444 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59444  in
            (uu____59439, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59466);
               FStar_Parser_AST.prange = uu____59467;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59497 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59556 -> acc
        | FStar_Parser_AST.PatName uu____59559 -> acc
        | FStar_Parser_AST.PatOp uu____59560 -> acc
        | FStar_Parser_AST.PatConst uu____59561 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59578) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59584) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59593) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59610 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59610
        | FStar_Parser_AST.PatAscribed (pat,uu____59618) ->
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
               then (Prims.parse_int "0")
               else (Prims.parse_int "1"))
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____59700 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59742 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59791  ->
    match uu___432_59791 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59798 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59831  ->
    match uu____59831 with
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
      let uu____59913 =
        let uu____59930 =
          let uu____59933 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59933  in
        let uu____59934 =
          let uu____59945 =
            let uu____59954 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59954)  in
          [uu____59945]  in
        (uu____59930, uu____59934)  in
      FStar_Syntax_Syntax.Tm_app uu____59913  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____60003 =
        let uu____60020 =
          let uu____60023 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____60023  in
        let uu____60024 =
          let uu____60035 =
            let uu____60044 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____60044)  in
          [uu____60035]  in
        (uu____60020, uu____60024)  in
      FStar_Syntax_Syntax.Tm_app uu____60003  in
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
          let uu____60107 =
            let uu____60124 =
              let uu____60127 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60127  in
            let uu____60128 =
              let uu____60139 =
                let uu____60148 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60148)  in
              let uu____60156 =
                let uu____60167 =
                  let uu____60176 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60176)  in
                [uu____60167]  in
              uu____60139 :: uu____60156  in
            (uu____60124, uu____60128)  in
          FStar_Syntax_Syntax.Tm_app uu____60107  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60236 =
        let uu____60251 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60270  ->
               match uu____60270 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60281;
                    FStar_Syntax_Syntax.index = uu____60282;
                    FStar_Syntax_Syntax.sort = t;_},uu____60284)
                   ->
                   let uu____60292 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60292) uu____60251
         in
      FStar_All.pipe_right bs uu____60236  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60308 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60326 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60354 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60375,uu____60376,bs,t,uu____60379,uu____60380)
                            ->
                            let uu____60389 = bs_univnames bs  in
                            let uu____60392 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60389 uu____60392
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60395,uu____60396,t,uu____60398,uu____60399,uu____60400)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60407 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60354 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60416 = s  in
        let uu____60417 =
          let uu____60418 =
            let uu____60427 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60445,bs,t,lids1,lids2) ->
                          let uu___1027_60458 = se  in
                          let uu____60459 =
                            let uu____60460 =
                              let uu____60477 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60478 =
                                let uu____60479 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60479 t  in
                              (lid, uvs, uu____60477, uu____60478, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60460
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60459;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60458.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60458.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60458.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60458.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60493,t,tlid,n1,lids1) ->
                          let uu___1037_60504 = se  in
                          let uu____60505 =
                            let uu____60506 =
                              let uu____60522 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60522, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60506  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60505;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60504.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60504.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60504.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60504.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60526 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60427, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60418  in
        {
          FStar_Syntax_Syntax.sigel = uu____60417;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60416.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60416.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60416.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60416.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60533,t) ->
        let uvs =
          let uu____60536 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60536 FStar_Util.set_elements  in
        let uu___1046_60541 = s  in
        let uu____60542 =
          let uu____60543 =
            let uu____60550 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60550)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60543  in
        {
          FStar_Syntax_Syntax.sigel = uu____60542;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60541.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60541.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60541.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60541.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60574 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60577 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60584) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60617,(FStar_Util.Inl t,uu____60619),uu____60620)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60667,(FStar_Util.Inr c,uu____60669),uu____60670)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60717 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60718,(FStar_Util.Inl t,uu____60720),uu____60721) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60768,(FStar_Util.Inr c,uu____60770),uu____60771) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60818 -> empty_set  in
          FStar_Util.set_union uu____60574 uu____60577  in
        let all_lb_univs =
          let uu____60822 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60838 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60838) empty_set)
             in
          FStar_All.pipe_right uu____60822 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60848 = s  in
        let uu____60849 =
          let uu____60850 =
            let uu____60857 =
              let uu____60858 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60870 = lb  in
                        let uu____60871 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60874 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60870.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60871;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60870.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60874;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60870.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60870.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60858)  in
            (uu____60857, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60850  in
        {
          FStar_Syntax_Syntax.sigel = uu____60849;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60848.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60848.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60848.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60848.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60883,fml) ->
        let uvs =
          let uu____60886 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60886 FStar_Util.set_elements  in
        let uu___1112_60891 = s  in
        let uu____60892 =
          let uu____60893 =
            let uu____60900 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60900)  in
          FStar_Syntax_Syntax.Sig_assume uu____60893  in
        {
          FStar_Syntax_Syntax.sigel = uu____60892;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60891.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60891.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60891.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60891.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60902,bs,c,flags) ->
        let uvs =
          let uu____60911 =
            let uu____60914 = bs_univnames bs  in
            let uu____60917 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60914 uu____60917  in
          FStar_All.pipe_right uu____60911 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60925 = s  in
        let uu____60926 =
          let uu____60927 =
            let uu____60940 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60941 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60940, uu____60941, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60927  in
        {
          FStar_Syntax_Syntax.sigel = uu____60926;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60925.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60925.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60925.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60925.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60944 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60952  ->
    match uu___433_60952 with
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
    | "null_wp" -> true
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
    | uu____61003 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____61024 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____61024)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____61050 =
      let uu____61051 = unparen t  in uu____61051.FStar_Parser_AST.tm  in
    match uu____61050 with
    | FStar_Parser_AST.Wild  ->
        let uu____61057 =
          let uu____61058 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____61058  in
        FStar_Util.Inr uu____61057
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61071)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
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
             let uu____61162 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61162
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61179 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61179
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61195 =
               let uu____61201 =
                 let uu____61203 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61203
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61201)
                in
             FStar_Errors.raise_error uu____61195 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61212 ->
        let rec aux t1 univargs =
          let uu____61249 =
            let uu____61250 = unparen t1  in uu____61250.FStar_Parser_AST.tm
             in
          match uu____61249 with
          | FStar_Parser_AST.App (t2,targ,uu____61258) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61285  ->
                     match uu___434_61285 with
                     | FStar_Util.Inr uu____61292 -> true
                     | uu____61295 -> false) univargs
              then
                let uu____61303 =
                  let uu____61304 =
                    FStar_List.map
                      (fun uu___435_61314  ->
                         match uu___435_61314 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61304  in
                FStar_Util.Inr uu____61303
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61340  ->
                        match uu___436_61340 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61350 -> failwith "impossible")
                     univargs
                    in
                 let uu____61354 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61354)
          | uu____61370 ->
              let uu____61371 =
                let uu____61377 =
                  let uu____61379 =
                    let uu____61381 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61381 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61379  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61377)
                 in
              FStar_Errors.raise_error uu____61371 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61396 ->
        let uu____61397 =
          let uu____61403 =
            let uu____61405 =
              let uu____61407 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61407 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61405  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61403)  in
        FStar_Errors.raise_error uu____61397 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61448;_});
            FStar_Syntax_Syntax.pos = uu____61449;
            FStar_Syntax_Syntax.vars = uu____61450;_})::uu____61451
        ->
        let uu____61482 =
          let uu____61488 =
            let uu____61490 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61490
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61488)  in
        FStar_Errors.raise_error uu____61482 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61496 ->
        let uu____61515 =
          let uu____61521 =
            let uu____61523 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61523
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61521)  in
        FStar_Errors.raise_error uu____61515 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61536 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61536) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61564 = FStar_List.hd fields  in
        match uu____61564 with
        | (f,uu____61574) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61586 =
                match uu____61586 with
                | (f',uu____61592) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61594 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61594
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
              (let uu____61604 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61604);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61967 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61974 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61975 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61977,pats1) ->
              let aux out uu____62018 =
                match uu____62018 with
                | (p2,uu____62031) ->
                    let intersection =
                      let uu____62041 = pat_vars p2  in
                      FStar_Util.set_intersect uu____62041 out  in
                    let uu____62044 = FStar_Util.set_is_empty intersection
                       in
                    if uu____62044
                    then
                      let uu____62049 = pat_vars p2  in
                      FStar_Util.set_union out uu____62049
                    else
                      (let duplicate_bv =
                         let uu____62055 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____62055  in
                       let uu____62058 =
                         let uu____62064 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____62064)
                          in
                       FStar_Errors.raise_error uu____62058 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62088 = pat_vars p1  in
            FStar_All.pipe_right uu____62088 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62116 =
                let uu____62118 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62118  in
              if uu____62116
              then ()
              else
                (let nonlinear_vars =
                   let uu____62127 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62127  in
                 let first_nonlinear_var =
                   let uu____62131 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62131  in
                 let uu____62134 =
                   let uu____62140 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62140)  in
                 FStar_Errors.raise_error uu____62134 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62168 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62168 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62185 ->
            let uu____62188 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62188 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62339 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62363 =
              let uu____62364 =
                let uu____62365 =
                  let uu____62372 =
                    let uu____62373 =
                      let uu____62379 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62379, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62373  in
                  (uu____62372, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62365  in
              {
                FStar_Parser_AST.pat = uu____62364;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62363
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62399 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62402 = aux loc env1 p2  in
              match uu____62402 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62491 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62496 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62496.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62496.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62491.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62498 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62503 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62503.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62503.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62498.FStar_Syntax_Syntax.p)
                        }
                    | uu____62504 when top -> p4
                    | uu____62505 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62510 =
                    match binder with
                    | LetBinder uu____62531 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62556 = close_fun env1 t  in
                          desugar_term env1 uu____62556  in
                        let x1 =
                          let uu___1380_62558 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62558.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62558.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62510 with
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
            let uu____62626 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62626, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62640 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62640, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62664 = resolvex loc env1 x  in
            (match uu____62664 with
             | (loc1,env2,xbv) ->
                 let uu____62693 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62693, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62716 = resolvex loc env1 x  in
            (match uu____62716 with
             | (loc1,env2,xbv) ->
                 let uu____62745 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62745, [], imp))
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
            let uu____62760 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62760, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62790;_},args)
            ->
            let uu____62796 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62857  ->
                     match uu____62857 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62938 = aux loc1 env2 arg  in
                         (match uu____62938 with
                          | (loc2,env3,uu____62985,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62796 with
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
                 let uu____63117 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63117, annots, false))
        | FStar_Parser_AST.PatApp uu____63135 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63166 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63217  ->
                     match uu____63217 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63278 = aux loc1 env2 pat  in
                         (match uu____63278 with
                          | (loc2,env3,uu____63320,pat1,ans,uu____63323) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63166 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63420 =
                     let uu____63423 =
                       let uu____63430 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63430  in
                     let uu____63431 =
                       let uu____63432 =
                         let uu____63446 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63446, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63432  in
                     FStar_All.pipe_left uu____63423 uu____63431  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63480 =
                            let uu____63481 =
                              let uu____63495 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63495, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63481  in
                          FStar_All.pipe_left (pos_r r) uu____63480) pats1
                     uu____63420
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
            let uu____63553 =
              FStar_List.fold_left
                (fun uu____63613  ->
                   fun p2  ->
                     match uu____63613 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63695 = aux loc1 env2 p2  in
                         (match uu____63695 with
                          | (loc2,env3,uu____63742,pat,ans,uu____63745) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63553 with
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
                   | uu____63911 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63914 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63914, annots, false))
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
                   (fun uu____63995  ->
                      match uu____63995 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____64025  ->
                      match uu____64025 with
                      | (f,uu____64031) ->
                          let uu____64032 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____64058  ->
                                    match uu____64058 with
                                    | (g,uu____64065) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____64032 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64071,p2) ->
                               p2)))
               in
            let app =
              let uu____64078 =
                let uu____64079 =
                  let uu____64086 =
                    let uu____64087 =
                      let uu____64088 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64088  in
                    FStar_Parser_AST.mk_pattern uu____64087
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64086, args)  in
                FStar_Parser_AST.PatApp uu____64079  in
              FStar_Parser_AST.mk_pattern uu____64078
                p1.FStar_Parser_AST.prange
               in
            let uu____64091 = aux loc env1 app  in
            (match uu____64091 with
             | (env2,e,b,p2,annots,uu____64137) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64177 =
                         let uu____64178 =
                           let uu____64192 =
                             let uu___1528_64193 = fv  in
                             let uu____64194 =
                               let uu____64197 =
                                 let uu____64198 =
                                   let uu____64205 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64205)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64198
                                  in
                               FStar_Pervasives_Native.Some uu____64197  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64193.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64193.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64194
                             }  in
                           (uu____64192, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64178  in
                       FStar_All.pipe_left pos uu____64177
                   | uu____64231 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64317 = aux' true loc env1 p2  in
            (match uu____64317 with
             | (loc1,env2,var,p3,ans,uu____64361) ->
                 let uu____64376 =
                   FStar_List.fold_left
                     (fun uu____64425  ->
                        fun p4  ->
                          match uu____64425 with
                          | (loc2,env3,ps1) ->
                              let uu____64490 = aux' true loc2 env3 p4  in
                              (match uu____64490 with
                               | (loc3,env4,uu____64531,p5,ans1,uu____64534)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64376 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64695 ->
            let uu____64696 = aux' true loc env1 p1  in
            (match uu____64696 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64793 = aux_maybe_or env p  in
      match uu____64793 with
      | (env1,b,pats) ->
          ((let uu____64848 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64848
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
          let uu____64921 =
            let uu____64922 =
              let uu____64933 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64933, (ty, tacopt))  in
            LetBinder uu____64922  in
          (env, uu____64921, [])  in
        let op_to_ident x =
          let uu____64950 =
            let uu____64956 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64956, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64950  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64978 = op_to_ident x  in
              mklet uu____64978 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64980) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____64986;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65002 = op_to_ident x  in
              let uu____65003 = desugar_term env t  in
              mklet uu____65002 uu____65003 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____65005);
                 FStar_Parser_AST.prange = uu____65006;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65026 = desugar_term env t  in
              mklet x uu____65026 tacopt1
          | uu____65027 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____65040 = desugar_data_pat env p  in
           match uu____65040 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65069;
                      FStar_Syntax_Syntax.p = uu____65070;_},uu____65071)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65084;
                      FStar_Syntax_Syntax.p = uu____65085;_},uu____65086)::[]
                     -> []
                 | uu____65099 -> p1  in
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
  fun uu____65107  ->
    fun env  ->
      fun pat  ->
        let uu____65111 = desugar_data_pat env pat  in
        match uu____65111 with | (env1,uu____65127,pat1) -> (env1, pat1)

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
      let uu____65149 = desugar_term_aq env e  in
      match uu____65149 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65168 = desugar_typ_aq env e  in
      match uu____65168 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65178  ->
        fun range  ->
          match uu____65178 with
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
              ((let uu____65200 =
                  let uu____65202 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65202  in
                if uu____65200
                then
                  let uu____65205 =
                    let uu____65211 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65211)  in
                  FStar_Errors.log_issue range uu____65205
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
                  let uu____65232 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65232 range  in
                let lid1 =
                  let uu____65236 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65236 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65246 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65246 range  in
                           let private_fv =
                             let uu____65248 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65248 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65249 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65249.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65249.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65250 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65254 =
                        let uu____65260 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65260)
                         in
                      FStar_Errors.raise_error uu____65254 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65280 =
                  let uu____65287 =
                    let uu____65288 =
                      let uu____65305 =
                        let uu____65316 =
                          let uu____65325 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65325)  in
                        [uu____65316]  in
                      (lid1, uu____65305)  in
                    FStar_Syntax_Syntax.Tm_app uu____65288  in
                  FStar_Syntax_Syntax.mk uu____65287  in
                uu____65280 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65376 =
          let uu____65377 = unparen t  in uu____65377.FStar_Parser_AST.tm  in
        match uu____65376 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65378; FStar_Ident.ident = uu____65379;
              FStar_Ident.nsstr = uu____65380; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65385 ->
            let uu____65386 =
              let uu____65392 =
                let uu____65394 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65394  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65392)  in
            FStar_Errors.raise_error uu____65386 t.FStar_Parser_AST.range
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
          let uu___1725_65481 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65481.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65481.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65484 =
          let uu____65485 = unparen top  in uu____65485.FStar_Parser_AST.tm
           in
        match uu____65484 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65490 ->
            let uu____65499 = desugar_formula env top  in
            (uu____65499, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65508 = desugar_formula env t  in (uu____65508, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65517 = desugar_formula env t  in (uu____65517, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65544 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65544, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65546 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65546, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65555 =
                let uu____65556 =
                  let uu____65563 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65563, args)  in
                FStar_Parser_AST.Op uu____65556  in
              FStar_Parser_AST.mk_term uu____65555 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65568 =
              let uu____65569 =
                let uu____65570 =
                  let uu____65577 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65577, [e])  in
                FStar_Parser_AST.Op uu____65570  in
              FStar_Parser_AST.mk_term uu____65569 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65568
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65589 = FStar_Ident.text_of_id op_star  in
             uu____65589 = "*") &&
              (let uu____65594 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65594 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65611;_},t1::t2::[])
                  when
                  let uu____65617 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65617 FStar_Option.isNone ->
                  let uu____65624 = flatten1 t1  in
                  FStar_List.append uu____65624 [t2]
              | uu____65627 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65632 = top  in
              let uu____65633 =
                let uu____65634 =
                  let uu____65645 =
                    FStar_List.map (fun _65656  -> FStar_Util.Inr _65656)
                      terms
                     in
                  (uu____65645, rhs)  in
                FStar_Parser_AST.Sum uu____65634  in
              {
                FStar_Parser_AST.tm = uu____65633;
                FStar_Parser_AST.range =
                  (uu___1773_65632.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65632.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65664 =
              let uu____65665 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65665  in
            (uu____65664, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65671 =
              let uu____65677 =
                let uu____65679 =
                  let uu____65681 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65681 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65679  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65677)
               in
            FStar_Errors.raise_error uu____65671 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65696 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65696 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65703 =
                   let uu____65709 =
                     let uu____65711 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65711
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65709)
                    in
                 FStar_Errors.raise_error uu____65703
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65726 =
                     let uu____65751 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65813 = desugar_term_aq env t  in
                               match uu____65813 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65751 FStar_List.unzip  in
                   (match uu____65726 with
                    | (args1,aqs) ->
                        let uu____65946 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65946, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65963)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65980 =
              let uu___1802_65981 = top  in
              let uu____65982 =
                let uu____65983 =
                  let uu____65990 =
                    let uu___1804_65991 = top  in
                    let uu____65992 =
                      let uu____65993 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____65993  in
                    {
                      FStar_Parser_AST.tm = uu____65992;
                      FStar_Parser_AST.range =
                        (uu___1804_65991.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_65991.FStar_Parser_AST.level)
                    }  in
                  (uu____65990, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65983  in
              {
                FStar_Parser_AST.tm = uu____65982;
                FStar_Parser_AST.range =
                  (uu___1802_65981.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65981.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65980
        | FStar_Parser_AST.Construct (n1,(a,uu____66001)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____66021 =
                let uu___1814_66022 = top  in
                let uu____66023 =
                  let uu____66024 =
                    let uu____66031 =
                      let uu___1816_66032 = top  in
                      let uu____66033 =
                        let uu____66034 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____66034  in
                      {
                        FStar_Parser_AST.tm = uu____66033;
                        FStar_Parser_AST.range =
                          (uu___1816_66032.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_66032.FStar_Parser_AST.level)
                      }  in
                    (uu____66031, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____66024  in
                {
                  FStar_Parser_AST.tm = uu____66023;
                  FStar_Parser_AST.range =
                    (uu___1814_66022.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_66022.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____66021))
        | FStar_Parser_AST.Construct (n1,(a,uu____66042)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____66059 =
              let uu___1825_66060 = top  in
              let uu____66061 =
                let uu____66062 =
                  let uu____66069 =
                    let uu___1827_66070 = top  in
                    let uu____66071 =
                      let uu____66072 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66072  in
                    {
                      FStar_Parser_AST.tm = uu____66071;
                      FStar_Parser_AST.range =
                        (uu___1827_66070.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66070.FStar_Parser_AST.level)
                    }  in
                  (uu____66069, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____66062  in
              {
                FStar_Parser_AST.tm = uu____66061;
                FStar_Parser_AST.range =
                  (uu___1825_66060.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_66060.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____66059
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66078; FStar_Ident.ident = uu____66079;
              FStar_Ident.nsstr = uu____66080; FStar_Ident.str = "Type0";_}
            ->
            let uu____66085 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66085, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66086; FStar_Ident.ident = uu____66087;
              FStar_Ident.nsstr = uu____66088; FStar_Ident.str = "Type";_}
            ->
            let uu____66093 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66093, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66094; FStar_Ident.ident = uu____66095;
               FStar_Ident.nsstr = uu____66096; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66116 =
              let uu____66117 =
                let uu____66118 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66118  in
              mk1 uu____66117  in
            (uu____66116, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66119; FStar_Ident.ident = uu____66120;
              FStar_Ident.nsstr = uu____66121; FStar_Ident.str = "Effect";_}
            ->
            let uu____66126 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66126, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66127; FStar_Ident.ident = uu____66128;
              FStar_Ident.nsstr = uu____66129; FStar_Ident.str = "True";_}
            ->
            let uu____66134 =
              let uu____66135 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66135
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66134, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66136; FStar_Ident.ident = uu____66137;
              FStar_Ident.nsstr = uu____66138; FStar_Ident.str = "False";_}
            ->
            let uu____66143 =
              let uu____66144 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66144
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66143, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66147;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66150 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66150 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66159 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66159, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66161 =
                    let uu____66163 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66163 txt
                     in
                  failwith uu____66161))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66172 = desugar_name mk1 setpos env true l  in
              (uu____66172, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66181 = desugar_name mk1 setpos env true l  in
              (uu____66181, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66199 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66199 with
                | FStar_Pervasives_Native.Some uu____66209 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66217 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66217 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66235 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66256 =
                    let uu____66257 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66257  in
                  (uu____66256, noaqs)
              | uu____66263 ->
                  let uu____66271 =
                    let uu____66277 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66277)  in
                  FStar_Errors.raise_error uu____66271
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66287 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66287 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66294 =
                    let uu____66300 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66300)
                     in
                  FStar_Errors.raise_error uu____66294
                    top.FStar_Parser_AST.range
              | uu____66308 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66312 = desugar_name mk1 setpos env true lid'  in
                  (uu____66312, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66334 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66334 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66353 ->
                       let uu____66360 =
                         FStar_Util.take
                           (fun uu____66384  ->
                              match uu____66384 with
                              | (uu____66390,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66360 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66435 =
                              let uu____66460 =
                                FStar_List.map
                                  (fun uu____66503  ->
                                     match uu____66503 with
                                     | (t,imp) ->
                                         let uu____66520 =
                                           desugar_term_aq env t  in
                                         (match uu____66520 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66460
                                FStar_List.unzip
                               in
                            (match uu____66435 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66663 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66663, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66682 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66682 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66693 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66721  ->
                 match uu___437_66721 with
                 | FStar_Util.Inr uu____66727 -> true
                 | uu____66729 -> false) binders
            ->
            let terms =
              let uu____66738 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66755  ->
                        match uu___438_66755 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66761 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66738 [t]  in
            let uu____66763 =
              let uu____66788 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66845 = desugar_typ_aq env t1  in
                        match uu____66845 with
                        | (t',aq) ->
                            let uu____66856 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66856, aq)))
                 in
              FStar_All.pipe_right uu____66788 FStar_List.unzip  in
            (match uu____66763 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66966 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66966
                    in
                 let uu____66975 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66975, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____67002 =
              let uu____67019 =
                let uu____67026 =
                  let uu____67033 =
                    FStar_All.pipe_left
                      (fun _67042  -> FStar_Util.Inl _67042)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____67033]  in
                FStar_List.append binders uu____67026  in
              FStar_List.fold_left
                (fun uu____67087  ->
                   fun b  ->
                     match uu____67087 with
                     | (env1,tparams,typs) ->
                         let uu____67148 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67163 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67163)
                            in
                         (match uu____67148 with
                          | (xopt,t1) ->
                              let uu____67188 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67197 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67197)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67188 with
                               | (env2,x) ->
                                   let uu____67217 =
                                     let uu____67220 =
                                       let uu____67223 =
                                         let uu____67224 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67224
                                          in
                                       [uu____67223]  in
                                     FStar_List.append typs uu____67220  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67250 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67250.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67250.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67217)))) (env, [], [])
                uu____67019
               in
            (match uu____67002 with
             | (env1,uu____67278,targs) ->
                 let tup =
                   let uu____67301 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67301
                    in
                 let uu____67302 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67302, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67321 = uncurry binders t  in
            (match uu____67321 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67365 =
                   match uu___439_67365 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67382 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67382
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67406 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67406 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67439 = aux env [] bs  in (uu____67439, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67448 = desugar_binder env b  in
            (match uu____67448 with
             | (FStar_Pervasives_Native.None ,uu____67459) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67474 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67474 with
                  | ((x,uu____67490),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67503 =
                        let uu____67504 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67504  in
                      (uu____67503, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67583 = FStar_Util.set_is_empty i  in
                    if uu____67583
                    then
                      let uu____67588 = FStar_Util.set_union acc set1  in
                      aux uu____67588 sets2
                    else
                      (let uu____67593 =
                         let uu____67594 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67594  in
                       FStar_Pervasives_Native.Some uu____67593)
                 in
              let uu____67597 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67597 sets  in
            ((let uu____67601 = check_disjoint bvss  in
              match uu____67601 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67605 =
                    let uu____67611 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67611)
                     in
                  let uu____67615 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67605 uu____67615);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67623 =
                FStar_List.fold_left
                  (fun uu____67643  ->
                     fun pat  ->
                       match uu____67643 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67669,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67679 =
                                  let uu____67682 = free_type_vars env1 t  in
                                  FStar_List.append uu____67682 ftvs  in
                                (env1, uu____67679)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67687,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67698 =
                                  let uu____67701 = free_type_vars env1 t  in
                                  let uu____67704 =
                                    let uu____67707 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67707 ftvs  in
                                  FStar_List.append uu____67701 uu____67704
                                   in
                                (env1, uu____67698)
                            | uu____67712 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67623 with
              | (uu____67721,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67733 =
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
                    FStar_List.append uu____67733 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67790 =
                    match uu___440_67790 with
                    | [] ->
                        let uu____67817 = desugar_term_aq env1 body  in
                        (match uu____67817 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67854 =
                                       let uu____67855 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67855
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67854
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
                             let uu____67924 =
                               let uu____67927 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67927  in
                             (uu____67924, aq))
                    | p::rest ->
                        let uu____67942 = desugar_binding_pat env1 p  in
                        (match uu____67942 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67976)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____67991 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____68000 =
                               match b with
                               | LetBinder uu____68041 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68110) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68164 =
                                           let uu____68173 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68173, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68164
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68235,uu____68236) ->
                                              let tup2 =
                                                let uu____68238 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68238
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68243 =
                                                  let uu____68250 =
                                                    let uu____68251 =
                                                      let uu____68268 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68271 =
                                                        let uu____68282 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68291 =
                                                          let uu____68302 =
                                                            let uu____68311 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68311
                                                             in
                                                          [uu____68302]  in
                                                        uu____68282 ::
                                                          uu____68291
                                                         in
                                                      (uu____68268,
                                                        uu____68271)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68251
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68250
                                                   in
                                                uu____68243
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68362 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68362
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68413,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68415,pats)) ->
                                              let tupn =
                                                let uu____68460 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68460
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68473 =
                                                  let uu____68474 =
                                                    let uu____68491 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68494 =
                                                      let uu____68505 =
                                                        let uu____68516 =
                                                          let uu____68525 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68525
                                                           in
                                                        [uu____68516]  in
                                                      FStar_List.append args
                                                        uu____68505
                                                       in
                                                    (uu____68491,
                                                      uu____68494)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68474
                                                   in
                                                mk1 uu____68473  in
                                              let p2 =
                                                let uu____68573 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68573
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68620 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____68000 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68714,uu____68715,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68737 =
                let uu____68738 = unparen e  in
                uu____68738.FStar_Parser_AST.tm  in
              match uu____68737 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68748 ->
                  let uu____68749 = desugar_term_aq env e  in
                  (match uu____68749 with
                   | (head1,aq) ->
                       let uu____68762 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68762, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68769 ->
            let rec aux args aqs e =
              let uu____68846 =
                let uu____68847 = unparen e  in
                uu____68847.FStar_Parser_AST.tm  in
              match uu____68846 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68865 = desugar_term_aq env t  in
                  (match uu____68865 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68913 ->
                  let uu____68914 = desugar_term_aq env e  in
                  (match uu____68914 with
                   | (head1,aq) ->
                       let uu____68935 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68935, (join_aqs (aq :: aqs))))
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
            let uu____68998 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____68998
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
            let uu____69050 = desugar_term_aq env t  in
            (match uu____69050 with
             | (tm,s) ->
                 let uu____69061 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____69061, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____69067 =
              let uu____69080 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69080 then desugar_typ_aq else desugar_term_aq  in
            uu____69067 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69139 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69282  ->
                        match uu____69282 with
                        | (attr_opt,(p,def)) ->
                            let uu____69340 = is_app_pattern p  in
                            if uu____69340
                            then
                              let uu____69373 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69373, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69456 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69456, def1)
                               | uu____69501 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69539);
                                           FStar_Parser_AST.prange =
                                             uu____69540;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69589 =
                                            let uu____69610 =
                                              let uu____69615 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69615  in
                                            (uu____69610, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69589, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69707) ->
                                        if top_level
                                        then
                                          let uu____69743 =
                                            let uu____69764 =
                                              let uu____69769 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69769  in
                                            (uu____69764, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69743, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69860 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69893 =
                FStar_List.fold_left
                  (fun uu____69966  ->
                     fun uu____69967  ->
                       match (uu____69966, uu____69967) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70075,uu____70076),uu____70077))
                           ->
                           let uu____70194 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70220 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70220 with
                                  | (env2,xx) ->
                                      let uu____70239 =
                                        let uu____70242 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70242 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70239))
                             | FStar_Util.Inr l ->
                                 let uu____70250 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70250, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70194 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69893 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70398 =
                    match uu____70398 with
                    | (attrs_opt,(uu____70434,args,result_t),def) ->
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
                                let uu____70522 = is_comp_type env1 t  in
                                if uu____70522
                                then
                                  ((let uu____70526 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70536 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70536))
                                       in
                                    match uu____70526 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70543 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70546 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70546))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70543
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
                          | uu____70557 ->
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
                              let uu____70572 =
                                let uu____70573 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70573
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70572
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
                  let uu____70654 = desugar_term_aq env' body  in
                  (match uu____70654 with
                   | (body1,aq) ->
                       let uu____70667 =
                         let uu____70670 =
                           let uu____70671 =
                             let uu____70685 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70685)  in
                           FStar_Syntax_Syntax.Tm_let uu____70671  in
                         FStar_All.pipe_left mk1 uu____70670  in
                       (uu____70667, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70760 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70760 with
              | (env1,binder,pat1) ->
                  let uu____70782 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70808 = desugar_term_aq env1 t2  in
                        (match uu____70808 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70822 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70822
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70823 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70823, aq))
                    | LocalBinder (x,uu____70856) ->
                        let uu____70857 = desugar_term_aq env1 t2  in
                        (match uu____70857 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70871;
                                    FStar_Syntax_Syntax.p = uu____70872;_},uu____70873)::[]
                                   -> body1
                               | uu____70886 ->
                                   let uu____70889 =
                                     let uu____70896 =
                                       let uu____70897 =
                                         let uu____70920 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70923 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70920, uu____70923)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70897
                                        in
                                     FStar_Syntax_Syntax.mk uu____70896  in
                                   uu____70889 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70963 =
                               let uu____70966 =
                                 let uu____70967 =
                                   let uu____70981 =
                                     let uu____70984 =
                                       let uu____70985 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70985]  in
                                     FStar_Syntax_Subst.close uu____70984
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70981)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70967  in
                               FStar_All.pipe_left mk1 uu____70966  in
                             (uu____70963, aq))
                     in
                  (match uu____70782 with | (tm,aq) -> (tm, aq))
               in
            let uu____71047 = FStar_List.hd lbs  in
            (match uu____71047 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71091 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71091
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71107 =
                let uu____71108 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71108  in
              mk1 uu____71107  in
            let uu____71109 = desugar_term_aq env t1  in
            (match uu____71109 with
             | (t1',aq1) ->
                 let uu____71120 = desugar_term_aq env t2  in
                 (match uu____71120 with
                  | (t2',aq2) ->
                      let uu____71131 = desugar_term_aq env t3  in
                      (match uu____71131 with
                       | (t3',aq3) ->
                           let uu____71142 =
                             let uu____71143 =
                               let uu____71144 =
                                 let uu____71167 =
                                   let uu____71184 =
                                     let uu____71199 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71199,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71213 =
                                     let uu____71230 =
                                       let uu____71245 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71245,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71230]  in
                                   uu____71184 :: uu____71213  in
                                 (t1', uu____71167)  in
                               FStar_Syntax_Syntax.Tm_match uu____71144  in
                             mk1 uu____71143  in
                           (uu____71142, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71441 =
              match uu____71441 with
              | (pat,wopt,b) ->
                  let uu____71463 = desugar_match_pat env pat  in
                  (match uu____71463 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71494 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71494
                          in
                       let uu____71499 = desugar_term_aq env1 b  in
                       (match uu____71499 with
                        | (b1,aq) ->
                            let uu____71512 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71512, aq)))
               in
            let uu____71517 = desugar_term_aq env e  in
            (match uu____71517 with
             | (e1,aq) ->
                 let uu____71528 =
                   let uu____71559 =
                     let uu____71592 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71592 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71559
                     (fun uu____71810  ->
                        match uu____71810 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71528 with
                  | (brs,aqs) ->
                      let uu____72029 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____72029, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____72063 =
              let uu____72084 = is_comp_type env t  in
              if uu____72084
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72139 = desugar_term_aq env t  in
                 match uu____72139 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____72063 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72231 = desugar_term_aq env e  in
                 (match uu____72231 with
                  | (e1,aq) ->
                      let uu____72242 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72242, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72281,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72324 = FStar_List.hd fields  in
              match uu____72324 with | (f,uu____72336) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72382  ->
                        match uu____72382 with
                        | (g,uu____72389) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72396,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72410 =
                         let uu____72416 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72416)
                          in
                       FStar_Errors.raise_error uu____72410
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
                  let uu____72427 =
                    let uu____72438 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72469  ->
                              match uu____72469 with
                              | (f,uu____72479) ->
                                  let uu____72480 =
                                    let uu____72481 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72481
                                     in
                                  (uu____72480, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72438)  in
                  FStar_Parser_AST.Construct uu____72427
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72499 =
                      let uu____72500 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72500  in
                    FStar_Parser_AST.mk_term uu____72499
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72502 =
                      let uu____72515 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72545  ->
                                match uu____72545 with
                                | (f,uu____72555) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72515)  in
                    FStar_Parser_AST.Record uu____72502  in
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
            let uu____72615 = desugar_term_aq env recterm1  in
            (match uu____72615 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72631;
                         FStar_Syntax_Syntax.vars = uu____72632;_},args)
                      ->
                      let uu____72658 =
                        let uu____72659 =
                          let uu____72660 =
                            let uu____72677 =
                              let uu____72680 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72681 =
                                let uu____72684 =
                                  let uu____72685 =
                                    let uu____72692 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72692)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72685
                                   in
                                FStar_Pervasives_Native.Some uu____72684  in
                              FStar_Syntax_Syntax.fvar uu____72680
                                FStar_Syntax_Syntax.delta_constant
                                uu____72681
                               in
                            (uu____72677, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72660  in
                        FStar_All.pipe_left mk1 uu____72659  in
                      (uu____72658, s)
                  | uu____72721 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72725 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72725 with
              | (constrname,is_rec) ->
                  let uu____72744 = desugar_term_aq env e  in
                  (match uu____72744 with
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
                       let uu____72764 =
                         let uu____72765 =
                           let uu____72766 =
                             let uu____72783 =
                               let uu____72786 =
                                 let uu____72787 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72787
                                  in
                               FStar_Syntax_Syntax.fvar uu____72786
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72789 =
                               let uu____72800 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72800]  in
                             (uu____72783, uu____72789)  in
                           FStar_Syntax_Syntax.Tm_app uu____72766  in
                         FStar_All.pipe_left mk1 uu____72765  in
                       (uu____72764, s))))
        | FStar_Parser_AST.NamedTyp (uu____72837,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72847 =
              let uu____72848 = FStar_Syntax_Subst.compress tm  in
              uu____72848.FStar_Syntax_Syntax.n  in
            (match uu____72847 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72856 =
                   let uu___2520_72857 =
                     let uu____72858 =
                       let uu____72860 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72860  in
                     FStar_Syntax_Util.exp_string uu____72858  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72857.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72857.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72856, noaqs)
             | uu____72861 ->
                 let uu____72862 =
                   let uu____72868 =
                     let uu____72870 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72870
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72868)  in
                 FStar_Errors.raise_error uu____72862
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72879 = desugar_term_aq env e  in
            (match uu____72879 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72891 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72891, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72896 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72897 =
              let uu____72898 =
                let uu____72905 = desugar_term env e  in (bv, uu____72905)
                 in
              [uu____72898]  in
            (uu____72896, uu____72897)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72930 =
              let uu____72931 =
                let uu____72932 =
                  let uu____72939 = desugar_term env e  in (uu____72939, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72932  in
              FStar_All.pipe_left mk1 uu____72931  in
            (uu____72930, noaqs)
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
              let uu____72968 =
                let uu____72969 =
                  let uu____72976 =
                    let uu____72977 =
                      let uu____72978 =
                        let uu____72987 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____73000 =
                          let uu____73001 =
                            let uu____73002 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____73002  in
                          FStar_Parser_AST.mk_term uu____73001
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____72987, uu____73000,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72978  in
                    FStar_Parser_AST.mk_term uu____72977
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72976)  in
                FStar_Parser_AST.Abs uu____72969  in
              FStar_Parser_AST.mk_term uu____72968
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
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
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
                init_expr.FStar_Parser_AST.range
               in
            let e1 =
              FStar_List.fold_left
                (fun e1  ->
                   fun uu____73048  ->
                     match uu____73048 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____73052 =
                           let uu____73059 =
                             let uu____73064 = eta_and_annot rel2  in
                             (uu____73064, FStar_Parser_AST.Nothing)  in
                           let uu____73065 =
                             let uu____73072 =
                               let uu____73079 =
                                 let uu____73084 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73084, FStar_Parser_AST.Nothing)  in
                               let uu____73085 =
                                 let uu____73092 =
                                   let uu____73097 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73097, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73092]  in
                               uu____73079 :: uu____73085  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73072
                              in
                           uu____73059 :: uu____73065  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____73052
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73119 =
                let uu____73126 =
                  let uu____73131 = FStar_Parser_AST.thunk e1  in
                  (uu____73131, FStar_Parser_AST.Nothing)  in
                [uu____73126]  in
              FStar_Parser_AST.mkApp finish1 uu____73119
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73140 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73141 = desugar_formula env top  in
            (uu____73141, noaqs)
        | uu____73142 ->
            let uu____73143 =
              let uu____73149 =
                let uu____73151 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73151  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73149)  in
            FStar_Errors.raise_error uu____73143 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73161 -> false
    | uu____73171 -> true

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
           (fun uu____73209  ->
              match uu____73209 with
              | (a,imp) ->
                  let uu____73222 = desugar_term env a  in
                  arg_withimp_e imp uu____73222))

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
          let is_requires uu____73259 =
            match uu____73259 with
            | (t1,uu____73266) ->
                let uu____73267 =
                  let uu____73268 = unparen t1  in
                  uu____73268.FStar_Parser_AST.tm  in
                (match uu____73267 with
                 | FStar_Parser_AST.Requires uu____73270 -> true
                 | uu____73279 -> false)
             in
          let is_ensures uu____73291 =
            match uu____73291 with
            | (t1,uu____73298) ->
                let uu____73299 =
                  let uu____73300 = unparen t1  in
                  uu____73300.FStar_Parser_AST.tm  in
                (match uu____73299 with
                 | FStar_Parser_AST.Ensures uu____73302 -> true
                 | uu____73311 -> false)
             in
          let is_app head1 uu____73329 =
            match uu____73329 with
            | (t1,uu____73337) ->
                let uu____73338 =
                  let uu____73339 = unparen t1  in
                  uu____73339.FStar_Parser_AST.tm  in
                (match uu____73338 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73342;
                        FStar_Parser_AST.level = uu____73343;_},uu____73344,uu____73345)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73347 -> false)
             in
          let is_smt_pat uu____73359 =
            match uu____73359 with
            | (t1,uu____73366) ->
                let uu____73367 =
                  let uu____73368 = unparen t1  in
                  uu____73368.FStar_Parser_AST.tm  in
                (match uu____73367 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73372);
                               FStar_Parser_AST.range = uu____73373;
                               FStar_Parser_AST.level = uu____73374;_},uu____73375)::uu____73376::[])
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
                               FStar_Parser_AST.range = uu____73425;
                               FStar_Parser_AST.level = uu____73426;_},uu____73427)::uu____73428::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73461 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73496 = head_and_args t1  in
            match uu____73496 with
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
                     let thunk_ens uu____73589 =
                       match uu____73589 with
                       | (e,i) ->
                           let uu____73600 = FStar_Parser_AST.thunk e  in
                           (uu____73600, i)
                        in
                     let fail_lemma uu____73612 =
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
                           let uu____73718 =
                             let uu____73725 =
                               let uu____73732 = thunk_ens ens  in
                               [uu____73732; nil_pat]  in
                             req_true :: uu____73725  in
                           unit_tm :: uu____73718
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73779 =
                             let uu____73786 =
                               let uu____73793 = thunk_ens ens  in
                               [uu____73793; nil_pat]  in
                             req :: uu____73786  in
                           unit_tm :: uu____73779
                       | ens::smtpat::[] when
                           (((let uu____73842 = is_requires ens  in
                              Prims.op_Negation uu____73842) &&
                               (let uu____73845 = is_smt_pat ens  in
                                Prims.op_Negation uu____73845))
                              &&
                              (let uu____73848 = is_decreases ens  in
                               Prims.op_Negation uu____73848))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73850 =
                             let uu____73857 =
                               let uu____73864 = thunk_ens ens  in
                               [uu____73864; smtpat]  in
                             req_true :: uu____73857  in
                           unit_tm :: uu____73850
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73911 =
                             let uu____73918 =
                               let uu____73925 = thunk_ens ens  in
                               [uu____73925; nil_pat; dec]  in
                             req_true :: uu____73918  in
                           unit_tm :: uu____73911
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73985 =
                             let uu____73992 =
                               let uu____73999 = thunk_ens ens  in
                               [uu____73999; smtpat; dec]  in
                             req_true :: uu____73992  in
                           unit_tm :: uu____73985
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____74059 =
                             let uu____74066 =
                               let uu____74073 = thunk_ens ens  in
                               [uu____74073; nil_pat; dec]  in
                             req :: uu____74066  in
                           unit_tm :: uu____74059
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74133 =
                             let uu____74140 =
                               let uu____74147 = thunk_ens ens  in
                               [uu____74147; smtpat]  in
                             req :: uu____74140  in
                           unit_tm :: uu____74133
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74212 =
                             let uu____74219 =
                               let uu____74226 = thunk_ens ens  in
                               [uu____74226; dec; smtpat]  in
                             req :: uu____74219  in
                           unit_tm :: uu____74212
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74288 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74288, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74316 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74316
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74319 =
                       let uu____74326 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74326, [])  in
                     (uu____74319, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74344 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74344
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74347 =
                       let uu____74354 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74354, [])  in
                     (uu____74347, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74376 =
                       let uu____74383 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74383, [])  in
                     (uu____74376, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74406 when allow_type_promotion ->
                     let default_effect =
                       let uu____74408 = FStar_Options.ml_ish ()  in
                       if uu____74408
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74414 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74414
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74421 =
                       let uu____74428 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74428, [])  in
                     (uu____74421, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74451 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74470 = pre_process_comp_typ t  in
          match uu____74470 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74522 =
                    let uu____74528 =
                      let uu____74530 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74530
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74528)
                     in
                  fail1 uu____74522)
               else ();
               (let is_universe uu____74546 =
                  match uu____74546 with
                  | (uu____74552,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74554 = FStar_Util.take is_universe args  in
                match uu____74554 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74613  ->
                           match uu____74613 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74620 =
                      let uu____74635 = FStar_List.hd args1  in
                      let uu____74644 = FStar_List.tl args1  in
                      (uu____74635, uu____74644)  in
                    (match uu____74620 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74699 =
                           let is_decrease uu____74738 =
                             match uu____74738 with
                             | (t1,uu____74749) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74760;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74761;_},uu____74762::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74801 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74699 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74918  ->
                                        match uu____74918 with
                                        | (t1,uu____74928) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74937,(arg,uu____74939)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74978 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____74999 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____75011 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____75011
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____75018 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____75018
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____75028 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75028
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____75035 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____75035
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____75042 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____75042
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____75049 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____75049
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75070 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75070
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
                                                    let uu____75161 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75161
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
                                              | uu____75182 -> pat  in
                                            let uu____75183 =
                                              let uu____75194 =
                                                let uu____75205 =
                                                  let uu____75214 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75214, aq)  in
                                                [uu____75205]  in
                                              ens :: uu____75194  in
                                            req :: uu____75183
                                        | uu____75255 -> rest2
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
        | uu____75287 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75309 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75309.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75309.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75351 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75351.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75351.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75351.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75414 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75414)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75427 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75427 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75437 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75437.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75437.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75463 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75477 =
                     let uu____75480 =
                       let uu____75481 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75481]  in
                     no_annot_abs uu____75480 body2  in
                   FStar_All.pipe_left setpos uu____75477  in
                 let uu____75502 =
                   let uu____75503 =
                     let uu____75520 =
                       let uu____75523 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75523
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75525 =
                       let uu____75536 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75536]  in
                     (uu____75520, uu____75525)  in
                   FStar_Syntax_Syntax.Tm_app uu____75503  in
                 FStar_All.pipe_left mk1 uu____75502)
        | uu____75575 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75656 = q (rest, pats, body)  in
              let uu____75663 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75656 uu____75663
                FStar_Parser_AST.Formula
               in
            let uu____75664 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75664 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75673 -> failwith "impossible"  in
      let uu____75677 =
        let uu____75678 = unparen f  in uu____75678.FStar_Parser_AST.tm  in
      match uu____75677 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75691,uu____75692) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75704,uu____75705) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75737 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75737
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75773 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75773
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75817 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75822 =
        FStar_List.fold_left
          (fun uu____75855  ->
             fun b  ->
               match uu____75855 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75899 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75899.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75899.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75899.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75914 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75914 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75932 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75932.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75932.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75933 =
                               let uu____75940 =
                                 let uu____75945 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75945)  in
                               uu____75940 :: out  in
                             (env2, uu____75933))
                    | uu____75956 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75822 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____76029 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76029)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____76034 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76034)
      | FStar_Parser_AST.TVariable x ->
          let uu____76038 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____76038)
      | FStar_Parser_AST.NoName t ->
          let uu____76042 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____76042)
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
      fun uu___441_76050  ->
        match uu___441_76050 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76072 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76072, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76089 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76089 with
             | (env1,a1) ->
                 let uu____76106 =
                   let uu____76113 = trans_aqual env1 imp  in
                   ((let uu___2962_76119 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76119.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76119.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76113)
                    in
                 (uu____76106, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76127  ->
      match uu___442_76127 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76131 =
            let uu____76132 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76132  in
          FStar_Pervasives_Native.Some uu____76131
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76148) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76150) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76153 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76171 = binder_ident b  in
         FStar_Common.list_of_option uu____76171) bs
  
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
               (fun uu___443_76208  ->
                  match uu___443_76208 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76213 -> false))
           in
        let quals2 q =
          let uu____76227 =
            (let uu____76231 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76231) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76227
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76248 = FStar_Ident.range_of_lid disc_name  in
                let uu____76249 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76248;
                  FStar_Syntax_Syntax.sigquals = uu____76249;
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
            let uu____76289 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76327  ->
                        match uu____76327 with
                        | (x,uu____76338) ->
                            let uu____76343 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76343 with
                             | (field_name,uu____76351) ->
                                 let only_decl =
                                   ((let uu____76356 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76356)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76358 =
                                        let uu____76360 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76360.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76358)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76378 =
                                       FStar_List.filter
                                         (fun uu___444_76382  ->
                                            match uu___444_76382 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76385 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76378
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76400  ->
                                             match uu___445_76400 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76405 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76408 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76408;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76415 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76415
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76426 =
                                        let uu____76431 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76431  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76426;
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
                                      let uu____76435 =
                                        let uu____76436 =
                                          let uu____76443 =
                                            let uu____76446 =
                                              let uu____76447 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76447
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76446]  in
                                          ((false, [lb]), uu____76443)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76436
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76435;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76289 FStar_List.flatten
  
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
            (lid,uu____76496,t,uu____76498,n1,uu____76500) when
            let uu____76507 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76507 ->
            let uu____76509 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76509 with
             | (formals,uu____76527) ->
                 (match formals with
                  | [] -> []
                  | uu____76556 ->
                      let filter_records uu___446_76572 =
                        match uu___446_76572 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76575,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76587 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76589 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76589 with
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
                      let uu____76601 = FStar_Util.first_N n1 formals  in
                      (match uu____76601 with
                       | (uu____76630,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76664 -> []
  
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
                    let uu____76743 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76743
                    then
                      let uu____76749 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76749
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76753 =
                      let uu____76758 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76758  in
                    let uu____76759 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76765 =
                          let uu____76768 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76768  in
                        FStar_Syntax_Util.arrow typars uu____76765
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76773 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76753;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76759;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76773;
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
          let tycon_id uu___447_76827 =
            match uu___447_76827 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76829,uu____76830) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76840,uu____76841,uu____76842) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76852,uu____76853,uu____76854) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76884,uu____76885,uu____76886) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76932) ->
                let uu____76933 =
                  let uu____76934 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76934  in
                FStar_Parser_AST.mk_term uu____76933 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76936 =
                  let uu____76937 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76937  in
                FStar_Parser_AST.mk_term uu____76936 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76939) ->
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
              | uu____76970 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76978 =
                     let uu____76979 =
                       let uu____76986 = binder_to_term b  in
                       (out, uu____76986, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76979  in
                   FStar_Parser_AST.mk_term uu____76978
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_76998 =
            match uu___448_76998 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____77055  ->
                       match uu____77055 with
                       | (x,t,uu____77066) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77072 =
                    let uu____77073 =
                      let uu____77074 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77074  in
                    FStar_Parser_AST.mk_term uu____77073
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77072 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77081 = binder_idents parms  in id1 ::
                    uu____77081
                   in
                (FStar_List.iter
                   (fun uu____77099  ->
                      match uu____77099 with
                      | (f,uu____77109,uu____77110) ->
                          let uu____77115 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77115
                          then
                            let uu____77120 =
                              let uu____77126 =
                                let uu____77128 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77128
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77126)
                               in
                            FStar_Errors.raise_error uu____77120
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77134 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77161  ->
                            match uu____77161 with
                            | (x,uu____77171,uu____77172) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77134)))
            | uu____77230 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77270 =
            match uu___449_77270 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77294 = typars_of_binders _env binders  in
                (match uu____77294 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77330 =
                         let uu____77331 =
                           let uu____77332 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77332  in
                         FStar_Parser_AST.mk_term uu____77331
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77330 binders  in
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
            | uu____77343 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77386 =
              FStar_List.fold_left
                (fun uu____77420  ->
                   fun uu____77421  ->
                     match (uu____77420, uu____77421) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77490 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77490 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77386 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77581 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77581
                | uu____77582 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77590 = desugar_abstract_tc quals env [] tc  in
              (match uu____77590 with
               | (uu____77603,uu____77604,se,uu____77606) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77609,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77628 =
                                 let uu____77630 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77630  in
                               if uu____77628
                               then
                                 let uu____77633 =
                                   let uu____77639 =
                                     let uu____77641 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77641
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77639)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77633
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
                           | uu____77654 ->
                               let uu____77655 =
                                 let uu____77662 =
                                   let uu____77663 =
                                     let uu____77678 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77678)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77663
                                    in
                                 FStar_Syntax_Syntax.mk uu____77662  in
                               uu____77655 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77694 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77694.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77694.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77694.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77695 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77699 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77699
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77712 = typars_of_binders env binders  in
              (match uu____77712 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77746 =
                           FStar_Util.for_some
                             (fun uu___450_77749  ->
                                match uu___450_77749 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77752 -> false) quals
                            in
                         if uu____77746
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77760 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77760
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77765 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77771  ->
                               match uu___451_77771 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77774 -> false))
                        in
                     if uu____77765
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77788 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77788
                     then
                       let uu____77794 =
                         let uu____77801 =
                           let uu____77802 = unparen t  in
                           uu____77802.FStar_Parser_AST.tm  in
                         match uu____77801 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77823 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77853)::args_rev ->
                                   let uu____77865 =
                                     let uu____77866 = unparen last_arg  in
                                     uu____77866.FStar_Parser_AST.tm  in
                                   (match uu____77865 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77894 -> ([], args))
                               | uu____77903 -> ([], args)  in
                             (match uu____77823 with
                              | (cattributes,args1) ->
                                  let uu____77942 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77942))
                         | uu____77953 -> (t, [])  in
                       match uu____77794 with
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
                                  (fun uu___452_77976  ->
                                     match uu___452_77976 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77979 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____77988)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____78012 = tycon_record_as_variant trec  in
              (match uu____78012 with
               | (t,fs) ->
                   let uu____78029 =
                     let uu____78032 =
                       let uu____78033 =
                         let uu____78042 =
                           let uu____78045 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____78045  in
                         (uu____78042, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____78033  in
                     uu____78032 :: quals  in
                   desugar_tycon env d uu____78029 [t])
          | uu____78050::uu____78051 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78221 = et  in
                match uu____78221 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78451 ->
                         let trec = tc  in
                         let uu____78475 = tycon_record_as_variant trec  in
                         (match uu____78475 with
                          | (t,fs) ->
                              let uu____78535 =
                                let uu____78538 =
                                  let uu____78539 =
                                    let uu____78548 =
                                      let uu____78551 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78551  in
                                    (uu____78548, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78539
                                   in
                                uu____78538 :: quals1  in
                              collect_tcs uu____78535 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78641 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78641 with
                          | (env2,uu____78702,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78855 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78855 with
                          | (env2,uu____78916,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____79044 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79094 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79094 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79609  ->
                             match uu___454_79609 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79675,uu____79676);
                                    FStar_Syntax_Syntax.sigrng = uu____79677;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79678;
                                    FStar_Syntax_Syntax.sigmeta = uu____79679;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79680;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79744 =
                                     typars_of_binders env1 binders  in
                                   match uu____79744 with
                                   | (env2,tpars1) ->
                                       let uu____79771 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79771 with
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
                                 let uu____79800 =
                                   let uu____79819 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79819)
                                    in
                                 [uu____79800]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79879);
                                    FStar_Syntax_Syntax.sigrng = uu____79880;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79882;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79883;_},constrs,tconstr,quals1)
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
                                 let uu____79984 = push_tparams env1 tpars
                                    in
                                 (match uu____79984 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____80051  ->
                                             match uu____80051 with
                                             | (x,uu____80063) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____80068 =
                                        let uu____80095 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80205  ->
                                                  match uu____80205 with
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
                                                        let uu____80265 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80265
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
                                                                uu___453_80276
                                                                 ->
                                                                match uu___453_80276
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80288
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80296 =
                                                        let uu____80315 =
                                                          let uu____80316 =
                                                            let uu____80317 =
                                                              let uu____80333
                                                                =
                                                                let uu____80334
                                                                  =
                                                                  let uu____80337
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80337
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80334
                                                                 in
                                                              (name, univs1,
                                                                uu____80333,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80317
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80316;
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
                                                          uu____80315)
                                                         in
                                                      (name, uu____80296)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80095
                                         in
                                      (match uu____80068 with
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
                             | uu____80553 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80681  ->
                             match uu____80681 with
                             | (name_doc,uu____80707,uu____80708) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80780  ->
                             match uu____80780 with
                             | (uu____80799,uu____80800,se) -> se))
                      in
                   let uu____80826 =
                     let uu____80833 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80833 rng
                      in
                   (match uu____80826 with
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
                               (fun uu____80895  ->
                                  match uu____80895 with
                                  | (uu____80916,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80964,tps,k,uu____80967,constrs)
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
                                      let uu____80988 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____81003 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____81020,uu____81021,uu____81022,uu____81023,uu____81024)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____81031
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____81003
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____81035 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_81042 
                                                          ->
                                                          match uu___455_81042
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____81044 ->
                                                              true
                                                          | uu____81054 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____81035))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____80988
                                  | uu____81056 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81073  ->
                                 match uu____81073 with
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
      let uu____81118 =
        FStar_List.fold_left
          (fun uu____81153  ->
             fun b  ->
               match uu____81153 with
               | (env1,binders1) ->
                   let uu____81197 = desugar_binder env1 b  in
                   (match uu____81197 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81220 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81220 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81273 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81118 with
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
          let uu____81377 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81384  ->
                    match uu___456_81384 with
                    | FStar_Syntax_Syntax.Reflectable uu____81386 -> true
                    | uu____81388 -> false))
             in
          if uu____81377
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81393 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81393
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
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____81434 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81434 with
      | (hd1,args) ->
          let uu____81487 =
            let uu____81502 =
              let uu____81503 = FStar_Syntax_Subst.compress hd1  in
              uu____81503.FStar_Syntax_Syntax.n  in
            (uu____81502, args)  in
          (match uu____81487 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81528)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81563 =
                 let uu____81568 =
                   let uu____81577 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81577 a1  in
                 uu____81568 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81563 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81607 =
                      let uu____81616 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81616, b)  in
                    FStar_Pervasives_Native.Some uu____81607
                | uu____81633 ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let b =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.fail_lax_attr
                  in
               FStar_Pervasives_Native.Some ([], b)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81687) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | uu____81722 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81894 = desugar_binders monad_env eff_binders  in
                  match uu____81894 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81934 =
                          let uu____81936 =
                            let uu____81945 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81945  in
                          FStar_List.length uu____81936  in
                        uu____81934 = (Prims.parse_int "1")  in
                      let mandatory_members =
                        let rr_members = ["repr"; "return"; "bind"]  in
                        if for_free
                        then rr_members
                        else
                          FStar_List.append rr_members
                            ["return_wp";
                            "bind_wp";
                            "if_then_else";
                            "ite_wp";
                            "stronger";
                            "close_wp";
                            "assert_p";
                            "assume_p";
                            "null_wp";
                            "trivial"]
                         in
                      let name_of_eff_decl decl =
                        match decl.FStar_Parser_AST.d with
                        | FStar_Parser_AST.Tycon
                            (uu____82029,uu____82030,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____82032,uu____82033,uu____82034),uu____82035)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82072 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82075 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82087 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82087 mandatory_members)
                          eff_decls
                         in
                      (match uu____82075 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82106 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82135  ->
                                     fun decl  ->
                                       match uu____82135 with
                                       | (env2,out) ->
                                           let uu____82155 =
                                             desugar_decl env2 decl  in
                                           (match uu____82155 with
                                            | (env3,ses) ->
                                                let uu____82168 =
                                                  let uu____82171 =
                                                    FStar_List.hd ses  in
                                                  uu____82171 :: out  in
                                                (env3, uu____82168)))
                                  (env1, []))
                              in
                           (match uu____82106 with
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
                                              (uu____82240,uu____82241,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82244,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82245,(def,uu____82247)::
                                                      (cps_type,uu____82249)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82250;
                                                   FStar_Parser_AST.level =
                                                     uu____82251;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82307 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82307 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82345 =
                                                     let uu____82346 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82347 =
                                                       let uu____82348 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82348
                                                        in
                                                     let uu____82355 =
                                                       let uu____82356 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82356
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82346;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82347;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82355
                                                     }  in
                                                   (uu____82345, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82365,uu____82366,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82369,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82408 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82408 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82446 =
                                                     let uu____82447 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82448 =
                                                       let uu____82449 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82449
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82447;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82448;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82446, doc1))
                                          | uu____82458 ->
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
                                let lookup1 s =
                                  let l =
                                    let uu____82494 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82494
                                     in
                                  let uu____82496 =
                                    let uu____82497 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82497
                                     in
                                  ([], uu____82496)  in
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
                                  if for_free
                                  then
                                    let dummy_tscheme =
                                      let uu____82515 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82515)  in
                                    let uu____82522 =
                                      let uu____82523 =
                                        let uu____82524 =
                                          let uu____82525 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82525
                                           in
                                        let uu____82535 = lookup1 "return"
                                           in
                                        let uu____82537 = lookup1 "bind"  in
                                        let uu____82539 =
                                          FStar_List.map (desugar_term env2)
                                            attrs
                                           in
                                        {
                                          FStar_Syntax_Syntax.cattributes =
                                            [];
                                          FStar_Syntax_Syntax.mname = mname;
                                          FStar_Syntax_Syntax.univs = [];
                                          FStar_Syntax_Syntax.binders =
                                            binders1;
                                          FStar_Syntax_Syntax.signature =
                                            eff_t1;
                                          FStar_Syntax_Syntax.ret_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.bind_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.if_then_else =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.ite_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.stronger =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.close_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assert_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assume_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.null_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.trivial =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.repr =
                                            uu____82524;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82535;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82537;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82539
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82523
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82522;
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange);
                                      FStar_Syntax_Syntax.sigquals =
                                        qualifiers;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = []
                                    }
                                  else
                                    (let rr =
                                       FStar_Util.for_some
                                         (fun uu___457_82547  ->
                                            match uu___457_82547 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82550 -> true
                                            | uu____82552 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82567 =
                                       let uu____82568 =
                                         let uu____82569 =
                                           lookup1 "return_wp"  in
                                         let uu____82571 = lookup1 "bind_wp"
                                            in
                                         let uu____82573 =
                                           lookup1 "if_then_else"  in
                                         let uu____82575 = lookup1 "ite_wp"
                                            in
                                         let uu____82577 = lookup1 "stronger"
                                            in
                                         let uu____82579 = lookup1 "close_wp"
                                            in
                                         let uu____82581 = lookup1 "assert_p"
                                            in
                                         let uu____82583 = lookup1 "assume_p"
                                            in
                                         let uu____82585 = lookup1 "null_wp"
                                            in
                                         let uu____82587 = lookup1 "trivial"
                                            in
                                         let uu____82589 =
                                           if rr
                                           then
                                             let uu____82591 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82591
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82609 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82614 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82619 =
                                           FStar_List.map (desugar_term env2)
                                             attrs
                                            in
                                         {
                                           FStar_Syntax_Syntax.cattributes =
                                             [];
                                           FStar_Syntax_Syntax.mname = mname;
                                           FStar_Syntax_Syntax.univs = [];
                                           FStar_Syntax_Syntax.binders =
                                             binders1;
                                           FStar_Syntax_Syntax.signature =
                                             eff_t1;
                                           FStar_Syntax_Syntax.ret_wp =
                                             uu____82569;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82571;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82573;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82575;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82577;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82579;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82581;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82583;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82585;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82587;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82589;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82609;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82614;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82619
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82568
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82567;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     })
                                   in
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
                                          fun uu____82645  ->
                                            match uu____82645 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82659 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82659
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
                let uu____82683 = desugar_binders env1 eff_binders  in
                match uu____82683 with
                | (env2,binders) ->
                    let uu____82720 =
                      let uu____82731 = head_and_args defn  in
                      match uu____82731 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82768 ->
                                let uu____82769 =
                                  let uu____82775 =
                                    let uu____82777 =
                                      let uu____82779 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82779 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82777  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82775)
                                   in
                                FStar_Errors.raise_error uu____82769
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82785 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82815)::args_rev ->
                                let uu____82827 =
                                  let uu____82828 = unparen last_arg  in
                                  uu____82828.FStar_Parser_AST.tm  in
                                (match uu____82827 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82856 -> ([], args))
                            | uu____82865 -> ([], args)  in
                          (match uu____82785 with
                           | (cattributes,args1) ->
                               let uu____82908 = desugar_args env2 args1  in
                               let uu____82909 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82908, uu____82909))
                       in
                    (match uu____82720 with
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
                          (let uu____82949 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82949 with
                           | (ed_binders,uu____82963,ed_binders_opening) ->
                               let sub' shift_n uu____82982 =
                                 match uu____82982 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____82997 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____82997 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____83001 =
                                       let uu____83002 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____83002)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____83001
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____83023 =
                                   let uu____83024 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____83024
                                    in
                                 let uu____83039 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____83040 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____83041 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____83042 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____83043 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____83044 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____83045 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____83046 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____83047 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____83048 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____83049 =
                                   let uu____83050 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____83050
                                    in
                                 let uu____83065 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____83066 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____83067 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83083 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83084 =
                                          let uu____83085 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83085
                                           in
                                        let uu____83106 =
                                          let uu____83107 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83107
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83083;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83084;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83106
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____83023;
                                   FStar_Syntax_Syntax.ret_wp = uu____83039;
                                   FStar_Syntax_Syntax.bind_wp = uu____83040;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____83041;
                                   FStar_Syntax_Syntax.ite_wp = uu____83042;
                                   FStar_Syntax_Syntax.stronger = uu____83043;
                                   FStar_Syntax_Syntax.close_wp = uu____83044;
                                   FStar_Syntax_Syntax.assert_p = uu____83045;
                                   FStar_Syntax_Syntax.assume_p = uu____83046;
                                   FStar_Syntax_Syntax.null_wp = uu____83047;
                                   FStar_Syntax_Syntax.trivial = uu____83048;
                                   FStar_Syntax_Syntax.repr = uu____83049;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____83065;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____83066;
                                   FStar_Syntax_Syntax.actions = uu____83067;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83131 =
                                     let uu____83133 =
                                       let uu____83142 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83142
                                        in
                                     FStar_List.length uu____83133  in
                                   uu____83131 = (Prims.parse_int "1")  in
                                 let uu____83175 =
                                   let uu____83178 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83178 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (if for_free
                                      then
                                        FStar_Syntax_Syntax.Sig_new_effect_for_free
                                          ed1
                                      else
                                        FStar_Syntax_Syntax.Sig_new_effect
                                          ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____83175;
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
                                             let uu____83202 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83202
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83204 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83204
                                 then
                                   let reflect_lid =
                                     let uu____83211 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83211
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____83223 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83223 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83308 ->
              let uu____83311 =
                let uu____83313 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83313
                 in
              Prims.op_Hat "\n  " uu____83311
          | uu____83316 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83335  ->
               match uu____83335 with
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
          let uu____83380 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83380
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83383 =
          let uu____83394 = FStar_Syntax_Syntax.as_arg arg  in [uu____83394]
           in
        FStar_Syntax_Util.mk_app fv uu____83383

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83425 = desugar_decl_noattrs env d  in
      match uu____83425 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83443 = mk_comment_attr d  in uu____83443 :: attrs1  in
          let uu____83444 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83454 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83454.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83454.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83454.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83454.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83457 = sigelt  in
                      let uu____83458 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83464 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83464) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83457.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83457.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83457.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83457.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83458
                      })) sigelts
             in
          (env1, uu____83444)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83490 = desugar_decl_aux env d  in
      match uu____83490 with
      | (env1,ses) ->
          let uu____83501 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83501)

and (desugar_decl_noattrs :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
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
      | FStar_Parser_AST.Fsdoc uu____83529 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83534 = FStar_Syntax_DsEnv.iface env  in
          if uu____83534
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83549 =
               let uu____83551 =
                 let uu____83553 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83554 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83553
                   uu____83554
                  in
               Prims.op_Negation uu____83551  in
             if uu____83549
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83568 =
                  let uu____83570 =
                    let uu____83572 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83572 lid  in
                  Prims.op_Negation uu____83570  in
                if uu____83568
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83586 =
                     let uu____83588 =
                       let uu____83590 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83590
                         lid
                        in
                     Prims.op_Negation uu____83588  in
                   if uu____83586
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83608 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83608, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83649,uu____83650)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83689 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83716  ->
                 match uu____83716 with | (x,uu____83724) -> x) tcs
             in
          let uu____83729 =
            let uu____83734 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83734 tcs1  in
          (match uu____83729 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83751 =
                   let uu____83752 =
                     let uu____83759 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83759  in
                   [uu____83752]  in
                 let uu____83772 =
                   let uu____83775 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83778 =
                     let uu____83789 =
                       let uu____83798 =
                         let uu____83799 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83799  in
                       FStar_Syntax_Syntax.as_arg uu____83798  in
                     [uu____83789]  in
                   FStar_Syntax_Util.mk_app uu____83775 uu____83778  in
                 FStar_Syntax_Util.abs uu____83751 uu____83772
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83839,id1))::uu____83841 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83844::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83848 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83848 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83854 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83854]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83875) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83885,uu____83886,uu____83887,uu____83888,uu____83889)
                     ->
                     let uu____83898 =
                       let uu____83899 =
                         let uu____83900 =
                           let uu____83907 = mkclass lid  in
                           (meths, uu____83907)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83900  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83899;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83898]
                 | uu____83910 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83944;
                    FStar_Parser_AST.prange = uu____83945;_},uu____83946)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83956;
                    FStar_Parser_AST.prange = uu____83957;_},uu____83958)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83974;
                         FStar_Parser_AST.prange = uu____83975;_},uu____83976);
                    FStar_Parser_AST.prange = uu____83977;_},uu____83978)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____84000;
                         FStar_Parser_AST.prange = uu____84001;_},uu____84002);
                    FStar_Parser_AST.prange = uu____84003;_},uu____84004)::[]
                   -> false
               | (p,uu____84033)::[] ->
                   let uu____84042 = is_app_pattern p  in
                   Prims.op_Negation uu____84042
               | uu____84044 -> false)
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
            let uu____84119 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84119 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84132 =
                     let uu____84133 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84133.FStar_Syntax_Syntax.n  in
                   match uu____84132 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84143) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let quals1 =
                         match quals with
                         | uu____84179::uu____84180 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84183 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84199  ->
                                     match uu___458_84199 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84202;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84203;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84204;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84205;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84206;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84207;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84208;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84220;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84221;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84222;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84223;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84224;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84225;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84239 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84272  ->
                                   match uu____84272 with
                                   | (uu____84286,(uu____84287,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84239
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84307 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84307
                         then
                           let uu____84313 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84328 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84330 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84330.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84330.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84328.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84313)
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
                           FStar_Syntax_Syntax.sigattrs = attrs
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
                   | uu____84360 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84368 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84387 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84368 with
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
                       let uu___4019_84424 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84424.FStar_Parser_AST.prange)
                       }
                   | uu____84431 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84438 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84438.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84438.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84438.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84474 id1 =
                   match uu____84474 with
                   | (env1,ses) ->
                       let main =
                         let uu____84495 =
                           let uu____84496 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84496  in
                         FStar_Parser_AST.mk_term uu____84495
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
                       let uu____84546 = desugar_decl env1 id_decl  in
                       (match uu____84546 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84564 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84564 FStar_Util.set_elements
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
            let uu____84588 = close_fun env t  in
            desugar_term env uu____84588  in
          let quals1 =
            let uu____84592 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84592
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84604 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84604;
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
                let uu____84618 =
                  let uu____84627 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84627]  in
                let uu____84646 =
                  let uu____84649 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84649
                   in
                FStar_Syntax_Util.arrow uu____84618 uu____84646
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
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
            let uu____84704 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84704 with
            | FStar_Pervasives_Native.None  ->
                let uu____84707 =
                  let uu____84713 =
                    let uu____84715 =
                      let uu____84717 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84717 " not found"  in
                    Prims.op_Hat "Effect name " uu____84715  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84713)  in
                FStar_Errors.raise_error uu____84707
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84725 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84743 =
                  let uu____84746 =
                    let uu____84747 = desugar_term env t  in
                    ([], uu____84747)  in
                  FStar_Pervasives_Native.Some uu____84746  in
                (uu____84743, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84760 =
                  let uu____84763 =
                    let uu____84764 = desugar_term env wp  in
                    ([], uu____84764)  in
                  FStar_Pervasives_Native.Some uu____84763  in
                let uu____84771 =
                  let uu____84774 =
                    let uu____84775 = desugar_term env t  in
                    ([], uu____84775)  in
                  FStar_Pervasives_Native.Some uu____84774  in
                (uu____84760, uu____84771)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84787 =
                  let uu____84790 =
                    let uu____84791 = desugar_term env t  in
                    ([], uu____84791)  in
                  FStar_Pervasives_Native.Some uu____84790  in
                (FStar_Pervasives_Native.None, uu____84787)
             in
          (match uu____84725 with
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
            let uu____84825 =
              let uu____84826 =
                let uu____84833 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84833, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84826  in
            {
              FStar_Syntax_Syntax.sigel = uu____84825;
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
      let uu____84860 =
        FStar_List.fold_left
          (fun uu____84880  ->
             fun d  ->
               match uu____84880 with
               | (env1,sigelts) ->
                   let uu____84900 = desugar_decl env1 d  in
                   (match uu____84900 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84860 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84945 =
            match uu___460_84945 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84959,FStar_Syntax_Syntax.Sig_let uu____84960) ->
                     let uu____84973 =
                       let uu____84976 =
                         let uu___4152_84977 = se2  in
                         let uu____84978 =
                           let uu____84981 =
                             FStar_List.filter
                               (fun uu___459_84995  ->
                                  match uu___459_84995 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____85000;
                                           FStar_Syntax_Syntax.vars =
                                             uu____85001;_},uu____85002);
                                      FStar_Syntax_Syntax.pos = uu____85003;
                                      FStar_Syntax_Syntax.vars = uu____85004;_}
                                      when
                                      let uu____85031 =
                                        let uu____85033 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____85033
                                         in
                                      uu____85031 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____85037 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84981
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84977.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84977.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84977.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84977.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84978
                         }  in
                       uu____84976 :: se1 :: acc  in
                     forward uu____84973 sigelts1
                 | uu____85043 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____85051 = forward [] sigelts  in (env1, uu____85051)
  
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
          | (FStar_Pervasives_Native.None ,uu____85116) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85120;
               FStar_Syntax_Syntax.exports = uu____85121;
               FStar_Syntax_Syntax.is_interface = uu____85122;_},FStar_Parser_AST.Module
             (current_lid,uu____85124)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85133) ->
              let uu____85136 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85136
           in
        let uu____85141 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85183 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85183, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85205 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85205, mname, decls, false)
           in
        match uu____85141 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85247 = desugar_decls env2 decls  in
            (match uu____85247 with
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
          let uu____85315 =
            (FStar_Options.interactive ()) &&
              (let uu____85318 =
                 let uu____85320 =
                   let uu____85322 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85322  in
                 FStar_Util.get_file_extension uu____85320  in
               FStar_List.mem uu____85318 ["fsti"; "fsi"])
             in
          if uu____85315 then as_interface m else m  in
        let uu____85336 = desugar_modul_common curmod env m1  in
        match uu____85336 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85358 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85358, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85380 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85380 with
      | (env1,modul,pop_when_done) ->
          let uu____85397 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85397 with
           | (env2,modul1) ->
               ((let uu____85409 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85409
                 then
                   let uu____85412 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85412
                 else ());
                (let uu____85417 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85417, modul1))))
  
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
        (fun uu____85471  ->
           let uu____85472 = desugar_modul env modul  in
           match uu____85472 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85514  ->
           let uu____85515 = desugar_decls env decls  in
           match uu____85515 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85570  ->
             let uu____85571 = desugar_partial_modul modul env a_modul  in
             match uu____85571 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85670 ->
                  let t =
                    let uu____85680 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85680  in
                  let uu____85693 =
                    let uu____85694 = FStar_Syntax_Subst.compress t  in
                    uu____85694.FStar_Syntax_Syntax.n  in
                  (match uu____85693 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85706,uu____85707)
                       -> bs1
                   | uu____85732 -> failwith "Impossible")
               in
            let uu____85742 =
              let uu____85749 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85749
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85742 with
            | (binders,uu____85751,binders_opening) ->
                let erase_term t =
                  let uu____85759 =
                    let uu____85760 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85760  in
                  FStar_Syntax_Subst.close binders uu____85759  in
                let erase_tscheme uu____85778 =
                  match uu____85778 with
                  | (us,t) ->
                      let t1 =
                        let uu____85798 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85798 t  in
                      let uu____85801 =
                        let uu____85802 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85802  in
                      ([], uu____85801)
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
                    | uu____85825 ->
                        let bs =
                          let uu____85835 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85835  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85875 =
                          let uu____85876 =
                            let uu____85879 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85879  in
                          uu____85876.FStar_Syntax_Syntax.n  in
                        (match uu____85875 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85881,uu____85882) -> bs1
                         | uu____85907 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85915 =
                      let uu____85916 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85916  in
                    FStar_Syntax_Subst.close binders uu____85915  in
                  let uu___4311_85917 = action  in
                  let uu____85918 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85919 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85917.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85917.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85918;
                    FStar_Syntax_Syntax.action_typ = uu____85919
                  }  in
                let uu___4313_85920 = ed  in
                let uu____85921 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85922 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85923 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85924 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85925 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85926 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85927 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85928 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85929 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85930 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85931 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85932 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85933 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85934 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85935 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85936 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85920.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85920.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85921;
                  FStar_Syntax_Syntax.signature = uu____85922;
                  FStar_Syntax_Syntax.ret_wp = uu____85923;
                  FStar_Syntax_Syntax.bind_wp = uu____85924;
                  FStar_Syntax_Syntax.if_then_else = uu____85925;
                  FStar_Syntax_Syntax.ite_wp = uu____85926;
                  FStar_Syntax_Syntax.stronger = uu____85927;
                  FStar_Syntax_Syntax.close_wp = uu____85928;
                  FStar_Syntax_Syntax.assert_p = uu____85929;
                  FStar_Syntax_Syntax.assume_p = uu____85930;
                  FStar_Syntax_Syntax.null_wp = uu____85931;
                  FStar_Syntax_Syntax.trivial = uu____85932;
                  FStar_Syntax_Syntax.repr = uu____85933;
                  FStar_Syntax_Syntax.return_repr = uu____85934;
                  FStar_Syntax_Syntax.bind_repr = uu____85935;
                  FStar_Syntax_Syntax.actions = uu____85936;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85920.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85952 = se  in
                  let uu____85953 =
                    let uu____85954 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85954  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85953;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85952.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85952.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85952.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85952.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85958 = se  in
                  let uu____85959 =
                    let uu____85960 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85960
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85959;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85958.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85958.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85958.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85958.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85962 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85963 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85963 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85980 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85980
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85982 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85982)
  