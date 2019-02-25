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
             (fun uu____57496  ->
                match uu____57496 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57551  ->
                             match uu____57551 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57569 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57569 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57575 =
                                     let uu____57576 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57576]  in
                                   FStar_Syntax_Subst.close uu____57575
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
      fun uu___429_57633  ->
        match uu___429_57633 with
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
  fun uu___430_57653  ->
    match uu___430_57653 with
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
  fun uu___431_57671  ->
    match uu___431_57671 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57674 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57682 .
    FStar_Parser_AST.imp ->
      'Auu____57682 ->
        ('Auu____57682 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57708 .
    FStar_Parser_AST.imp ->
      'Auu____57708 ->
        ('Auu____57708 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57727 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57748 -> true
            | uu____57754 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57763 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57770 =
      let uu____57771 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57771  in
    FStar_Parser_AST.mk_term uu____57770 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57781 =
      let uu____57782 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57782  in
    FStar_Parser_AST.mk_term uu____57781 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57798 =
        let uu____57799 = unparen t  in uu____57799.FStar_Parser_AST.tm  in
      match uu____57798 with
      | FStar_Parser_AST.Name l ->
          let uu____57802 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57802 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57809) ->
          let uu____57822 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57822 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57829,uu____57830) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57835,uu____57836) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57841,t1) -> is_comp_type env t1
      | uu____57843 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____57944;
                            FStar_Syntax_Syntax.vars = uu____57945;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____57973 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____57973 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____57989 =
                               let uu____57990 =
                                 let uu____57993 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____57993  in
                               uu____57990.FStar_Syntax_Syntax.n  in
                             match uu____57989 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58016))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58023 -> msg
                           else msg  in
                         let uu____58026 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58026
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58031 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58031 " is deprecated"  in
                         let uu____58034 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58034
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58036 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58052 .
    'Auu____58052 ->
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
        let uu____58105 =
          let uu____58108 =
            let uu____58109 =
              let uu____58115 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58115, r)  in
            FStar_Ident.mk_ident uu____58109  in
          [uu____58108]  in
        FStar_All.pipe_right uu____58105 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58131 .
    env_t ->
      Prims.int ->
        'Auu____58131 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58169 =
              let uu____58170 =
                let uu____58171 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58171 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58170 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58169  in
          let fallback uu____58179 =
            let uu____58180 = FStar_Ident.text_of_id op  in
            match uu____58180 with
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
                let uu____58201 = FStar_Options.ml_ish ()  in
                if uu____58201
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
            | uu____58226 -> FStar_Pervasives_Native.None  in
          let uu____58228 =
            let uu____58231 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58237 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58237.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58237.FStar_Syntax_Syntax.vars)
                 }) env true uu____58231
             in
          match uu____58228 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58242 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58257 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58257
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58306 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58310 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58310 with | (env1,uu____58322) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58325,term) ->
          let uu____58327 = free_type_vars env term  in (env, uu____58327)
      | FStar_Parser_AST.TAnnotated (id1,uu____58333) ->
          let uu____58334 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58334 with | (env1,uu____58346) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58350 = free_type_vars env t  in (env, uu____58350)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58357 =
        let uu____58358 = unparen t  in uu____58358.FStar_Parser_AST.tm  in
      match uu____58357 with
      | FStar_Parser_AST.Labeled uu____58361 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58374 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58374 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58379 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58382 -> []
      | FStar_Parser_AST.Uvar uu____58383 -> []
      | FStar_Parser_AST.Var uu____58384 -> []
      | FStar_Parser_AST.Projector uu____58385 -> []
      | FStar_Parser_AST.Discrim uu____58390 -> []
      | FStar_Parser_AST.Name uu____58391 -> []
      | FStar_Parser_AST.Requires (t1,uu____58393) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58401) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58408,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58427,ts) ->
          FStar_List.collect
            (fun uu____58448  ->
               match uu____58448 with
               | (t1,uu____58456) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58457,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58465) ->
          let uu____58466 = free_type_vars env t1  in
          let uu____58469 = free_type_vars env t2  in
          FStar_List.append uu____58466 uu____58469
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58474 = free_type_vars_b env b  in
          (match uu____58474 with
           | (env1,f) ->
               let uu____58489 = free_type_vars env1 t1  in
               FStar_List.append f uu____58489)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58506 =
            FStar_List.fold_left
              (fun uu____58530  ->
                 fun bt  ->
                   match uu____58530 with
                   | (env1,free) ->
                       let uu____58554 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58569 = free_type_vars env1 body  in
                             (env1, uu____58569)
                          in
                       (match uu____58554 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58506 with
           | (env1,free) ->
               let uu____58598 = free_type_vars env1 body  in
               FStar_List.append free uu____58598)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58607 =
            FStar_List.fold_left
              (fun uu____58627  ->
                 fun binder  ->
                   match uu____58627 with
                   | (env1,free) ->
                       let uu____58647 = free_type_vars_b env1 binder  in
                       (match uu____58647 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58607 with
           | (env1,free) ->
               let uu____58678 = free_type_vars env1 body  in
               FStar_List.append free uu____58678)
      | FStar_Parser_AST.Project (t1,uu____58682) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58693 = free_type_vars env rel  in
          let uu____58696 =
            let uu____58699 = free_type_vars env init1  in
            let uu____58702 =
              FStar_List.collect
                (fun uu____58711  ->
                   match uu____58711 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58717 = free_type_vars env rel1  in
                       let uu____58720 =
                         let uu____58723 = free_type_vars env just  in
                         let uu____58726 = free_type_vars env next  in
                         FStar_List.append uu____58723 uu____58726  in
                       FStar_List.append uu____58717 uu____58720) steps
               in
            FStar_List.append uu____58699 uu____58702  in
          FStar_List.append uu____58693 uu____58696
      | FStar_Parser_AST.Abs uu____58729 -> []
      | FStar_Parser_AST.Let uu____58736 -> []
      | FStar_Parser_AST.LetOpen uu____58757 -> []
      | FStar_Parser_AST.If uu____58762 -> []
      | FStar_Parser_AST.QForall uu____58769 -> []
      | FStar_Parser_AST.QExists uu____58782 -> []
      | FStar_Parser_AST.Record uu____58795 -> []
      | FStar_Parser_AST.Match uu____58808 -> []
      | FStar_Parser_AST.TryWith uu____58823 -> []
      | FStar_Parser_AST.Bind uu____58838 -> []
      | FStar_Parser_AST.Quote uu____58845 -> []
      | FStar_Parser_AST.VQuote uu____58850 -> []
      | FStar_Parser_AST.Antiquote uu____58851 -> []
      | FStar_Parser_AST.Seq uu____58852 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58906 =
        let uu____58907 = unparen t1  in uu____58907.FStar_Parser_AST.tm  in
      match uu____58906 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____58949 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____58974 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____58974  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____58996 =
                     let uu____58997 =
                       let uu____59002 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59002)  in
                     FStar_Parser_AST.TAnnotated uu____58997  in
                   FStar_Parser_AST.mk_binder uu____58996
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
        let uu____59020 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59020  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59042 =
                     let uu____59043 =
                       let uu____59048 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59048)  in
                     FStar_Parser_AST.TAnnotated uu____59043  in
                   FStar_Parser_AST.mk_binder uu____59042
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59050 =
             let uu____59051 = unparen t  in uu____59051.FStar_Parser_AST.tm
              in
           match uu____59050 with
           | FStar_Parser_AST.Product uu____59052 -> t
           | uu____59059 ->
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
      | uu____59096 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59107 -> true
    | FStar_Parser_AST.PatTvar (uu____59111,uu____59112) -> true
    | FStar_Parser_AST.PatVar (uu____59118,uu____59119) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59126) -> is_var_pattern p1
    | uu____59139 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59150) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59163;
           FStar_Parser_AST.prange = uu____59164;_},uu____59165)
        -> true
    | uu____59177 -> false
  
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
    | uu____59193 -> p
  
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
            let uu____59266 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59266 with
             | (name,args,uu____59309) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59359);
               FStar_Parser_AST.prange = uu____59360;_},args)
            when is_top_level1 ->
            let uu____59370 =
              let uu____59375 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59375  in
            (uu____59370, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59397);
               FStar_Parser_AST.prange = uu____59398;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59428 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59487 -> acc
        | FStar_Parser_AST.PatName uu____59490 -> acc
        | FStar_Parser_AST.PatOp uu____59491 -> acc
        | FStar_Parser_AST.PatConst uu____59492 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59509) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59515) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59524) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59541 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59541
        | FStar_Parser_AST.PatAscribed (pat,uu____59549) ->
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
    match projectee with | LocalBinder _0 -> true | uu____59631 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59673 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59722  ->
    match uu___432_59722 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59729 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59762  ->
    match uu____59762 with
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
      let uu____59844 =
        let uu____59861 =
          let uu____59864 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59864  in
        let uu____59865 =
          let uu____59876 =
            let uu____59885 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59885)  in
          [uu____59876]  in
        (uu____59861, uu____59865)  in
      FStar_Syntax_Syntax.Tm_app uu____59844  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____59934 =
        let uu____59951 =
          let uu____59954 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59954  in
        let uu____59955 =
          let uu____59966 =
            let uu____59975 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59975)  in
          [uu____59966]  in
        (uu____59951, uu____59955)  in
      FStar_Syntax_Syntax.Tm_app uu____59934  in
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
          let uu____60038 =
            let uu____60055 =
              let uu____60058 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60058  in
            let uu____60059 =
              let uu____60070 =
                let uu____60079 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60079)  in
              let uu____60087 =
                let uu____60098 =
                  let uu____60107 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60107)  in
                [uu____60098]  in
              uu____60070 :: uu____60087  in
            (uu____60055, uu____60059)  in
          FStar_Syntax_Syntax.Tm_app uu____60038  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60167 =
        let uu____60182 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60201  ->
               match uu____60201 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60212;
                    FStar_Syntax_Syntax.index = uu____60213;
                    FStar_Syntax_Syntax.sort = t;_},uu____60215)
                   ->
                   let uu____60223 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60223) uu____60182
         in
      FStar_All.pipe_right bs uu____60167  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60239 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60257 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60285 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60306,uu____60307,bs,t,uu____60310,uu____60311)
                            ->
                            let uu____60320 = bs_univnames bs  in
                            let uu____60323 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60320 uu____60323
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60326,uu____60327,t,uu____60329,uu____60330,uu____60331)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60338 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60285 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60347 = s  in
        let uu____60348 =
          let uu____60349 =
            let uu____60358 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60376,bs,t,lids1,lids2) ->
                          let uu___1027_60389 = se  in
                          let uu____60390 =
                            let uu____60391 =
                              let uu____60408 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60409 =
                                let uu____60410 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60410 t  in
                              (lid, uvs, uu____60408, uu____60409, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60391
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60390;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60389.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60389.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60389.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60389.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60424,t,tlid,n1,lids1) ->
                          let uu___1037_60435 = se  in
                          let uu____60436 =
                            let uu____60437 =
                              let uu____60453 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60453, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60437  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60436;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60435.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60435.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60435.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60435.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60457 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60358, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60349  in
        {
          FStar_Syntax_Syntax.sigel = uu____60348;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60347.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60347.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60347.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60347.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60464,t) ->
        let uvs =
          let uu____60467 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60467 FStar_Util.set_elements  in
        let uu___1046_60472 = s  in
        let uu____60473 =
          let uu____60474 =
            let uu____60481 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60481)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60474  in
        {
          FStar_Syntax_Syntax.sigel = uu____60473;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60472.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60472.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60472.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60472.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60505 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60508 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60515) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60548,(FStar_Util.Inl t,uu____60550),uu____60551)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60598,(FStar_Util.Inr c,uu____60600),uu____60601)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60648 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60649,(FStar_Util.Inl t,uu____60651),uu____60652) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60699,(FStar_Util.Inr c,uu____60701),uu____60702) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60749 -> empty_set  in
          FStar_Util.set_union uu____60505 uu____60508  in
        let all_lb_univs =
          let uu____60753 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60769 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60769) empty_set)
             in
          FStar_All.pipe_right uu____60753 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60779 = s  in
        let uu____60780 =
          let uu____60781 =
            let uu____60788 =
              let uu____60789 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60801 = lb  in
                        let uu____60802 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60805 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60801.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60802;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60801.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60805;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60801.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60801.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60789)  in
            (uu____60788, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60781  in
        {
          FStar_Syntax_Syntax.sigel = uu____60780;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60779.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60779.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60779.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60779.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60814,fml) ->
        let uvs =
          let uu____60817 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60817 FStar_Util.set_elements  in
        let uu___1112_60822 = s  in
        let uu____60823 =
          let uu____60824 =
            let uu____60831 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60831)  in
          FStar_Syntax_Syntax.Sig_assume uu____60824  in
        {
          FStar_Syntax_Syntax.sigel = uu____60823;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60822.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60822.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60822.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60822.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60833,bs,c,flags) ->
        let uvs =
          let uu____60842 =
            let uu____60845 = bs_univnames bs  in
            let uu____60848 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60845 uu____60848  in
          FStar_All.pipe_right uu____60842 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60856 = s  in
        let uu____60857 =
          let uu____60858 =
            let uu____60871 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60872 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60871, uu____60872, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60858  in
        {
          FStar_Syntax_Syntax.sigel = uu____60857;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60856.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60856.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60856.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60856.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60875 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60883  ->
    match uu___433_60883 with
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
    | uu____60934 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____60955 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____60955)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____60981 =
      let uu____60982 = unparen t  in uu____60982.FStar_Parser_AST.tm  in
    match uu____60981 with
    | FStar_Parser_AST.Wild  ->
        let uu____60988 =
          let uu____60989 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____60989  in
        FStar_Util.Inr uu____60988
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61002)) ->
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
             let uu____61093 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61093
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61110 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61110
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61126 =
               let uu____61132 =
                 let uu____61134 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61134
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61132)
                in
             FStar_Errors.raise_error uu____61126 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61143 ->
        let rec aux t1 univargs =
          let uu____61180 =
            let uu____61181 = unparen t1  in uu____61181.FStar_Parser_AST.tm
             in
          match uu____61180 with
          | FStar_Parser_AST.App (t2,targ,uu____61189) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61216  ->
                     match uu___434_61216 with
                     | FStar_Util.Inr uu____61223 -> true
                     | uu____61226 -> false) univargs
              then
                let uu____61234 =
                  let uu____61235 =
                    FStar_List.map
                      (fun uu___435_61245  ->
                         match uu___435_61245 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61235  in
                FStar_Util.Inr uu____61234
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61271  ->
                        match uu___436_61271 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61281 -> failwith "impossible")
                     univargs
                    in
                 let uu____61285 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61285)
          | uu____61301 ->
              let uu____61302 =
                let uu____61308 =
                  let uu____61310 =
                    let uu____61312 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61312 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61310  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61308)
                 in
              FStar_Errors.raise_error uu____61302 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61327 ->
        let uu____61328 =
          let uu____61334 =
            let uu____61336 =
              let uu____61338 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61338 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61336  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61334)  in
        FStar_Errors.raise_error uu____61328 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61379;_});
            FStar_Syntax_Syntax.pos = uu____61380;
            FStar_Syntax_Syntax.vars = uu____61381;_})::uu____61382
        ->
        let uu____61413 =
          let uu____61419 =
            let uu____61421 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61421
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61419)  in
        FStar_Errors.raise_error uu____61413 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61427 ->
        let uu____61446 =
          let uu____61452 =
            let uu____61454 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61454
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61452)  in
        FStar_Errors.raise_error uu____61446 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61467 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61467) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61495 = FStar_List.hd fields  in
        match uu____61495 with
        | (f,uu____61505) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61517 =
                match uu____61517 with
                | (f',uu____61523) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61525 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61525
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
              (let uu____61535 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61535);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61898 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61905 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61906 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61908,pats1) ->
              let aux out uu____61949 =
                match uu____61949 with
                | (p2,uu____61962) ->
                    let intersection =
                      let uu____61972 = pat_vars p2  in
                      FStar_Util.set_intersect uu____61972 out  in
                    let uu____61975 = FStar_Util.set_is_empty intersection
                       in
                    if uu____61975
                    then
                      let uu____61980 = pat_vars p2  in
                      FStar_Util.set_union out uu____61980
                    else
                      (let duplicate_bv =
                         let uu____61986 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____61986  in
                       let uu____61989 =
                         let uu____61995 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____61995)
                          in
                       FStar_Errors.raise_error uu____61989 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62019 = pat_vars p1  in
            FStar_All.pipe_right uu____62019 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62047 =
                let uu____62049 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62049  in
              if uu____62047
              then ()
              else
                (let nonlinear_vars =
                   let uu____62058 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62058  in
                 let first_nonlinear_var =
                   let uu____62062 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62062  in
                 let uu____62065 =
                   let uu____62071 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62071)  in
                 FStar_Errors.raise_error uu____62065 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62099 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62099 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62116 ->
            let uu____62119 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62119 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62270 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62294 =
              let uu____62295 =
                let uu____62296 =
                  let uu____62303 =
                    let uu____62304 =
                      let uu____62310 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62310, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62304  in
                  (uu____62303, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62296  in
              {
                FStar_Parser_AST.pat = uu____62295;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62294
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62330 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62333 = aux loc env1 p2  in
              match uu____62333 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62422 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62427 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62427.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62427.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62422.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62429 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62434 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62434.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62434.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62429.FStar_Syntax_Syntax.p)
                        }
                    | uu____62435 when top -> p4
                    | uu____62436 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62441 =
                    match binder with
                    | LetBinder uu____62462 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62487 = close_fun env1 t  in
                          desugar_term env1 uu____62487  in
                        let x1 =
                          let uu___1380_62489 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62489.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62489.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62441 with
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
            let uu____62557 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62557, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62571 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62571, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62595 = resolvex loc env1 x  in
            (match uu____62595 with
             | (loc1,env2,xbv) ->
                 let uu____62624 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62624, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62647 = resolvex loc env1 x  in
            (match uu____62647 with
             | (loc1,env2,xbv) ->
                 let uu____62676 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62676, [], imp))
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
            let uu____62691 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62691, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62721;_},args)
            ->
            let uu____62727 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62788  ->
                     match uu____62788 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62869 = aux loc1 env2 arg  in
                         (match uu____62869 with
                          | (loc2,env3,uu____62916,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62727 with
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
                 let uu____63048 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63048, annots, false))
        | FStar_Parser_AST.PatApp uu____63066 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63097 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63148  ->
                     match uu____63148 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63209 = aux loc1 env2 pat  in
                         (match uu____63209 with
                          | (loc2,env3,uu____63251,pat1,ans,uu____63254) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63097 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63351 =
                     let uu____63354 =
                       let uu____63361 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63361  in
                     let uu____63362 =
                       let uu____63363 =
                         let uu____63377 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63377, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63363  in
                     FStar_All.pipe_left uu____63354 uu____63362  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63411 =
                            let uu____63412 =
                              let uu____63426 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63426, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63412  in
                          FStar_All.pipe_left (pos_r r) uu____63411) pats1
                     uu____63351
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
            let uu____63484 =
              FStar_List.fold_left
                (fun uu____63544  ->
                   fun p2  ->
                     match uu____63544 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63626 = aux loc1 env2 p2  in
                         (match uu____63626 with
                          | (loc2,env3,uu____63673,pat,ans,uu____63676) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63484 with
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
                   | uu____63842 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63845 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63845, annots, false))
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
                   (fun uu____63926  ->
                      match uu____63926 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____63956  ->
                      match uu____63956 with
                      | (f,uu____63962) ->
                          let uu____63963 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____63989  ->
                                    match uu____63989 with
                                    | (g,uu____63996) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____63963 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64002,p2) ->
                               p2)))
               in
            let app =
              let uu____64009 =
                let uu____64010 =
                  let uu____64017 =
                    let uu____64018 =
                      let uu____64019 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64019  in
                    FStar_Parser_AST.mk_pattern uu____64018
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64017, args)  in
                FStar_Parser_AST.PatApp uu____64010  in
              FStar_Parser_AST.mk_pattern uu____64009
                p1.FStar_Parser_AST.prange
               in
            let uu____64022 = aux loc env1 app  in
            (match uu____64022 with
             | (env2,e,b,p2,annots,uu____64068) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64108 =
                         let uu____64109 =
                           let uu____64123 =
                             let uu___1528_64124 = fv  in
                             let uu____64125 =
                               let uu____64128 =
                                 let uu____64129 =
                                   let uu____64136 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64136)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64129
                                  in
                               FStar_Pervasives_Native.Some uu____64128  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64124.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64124.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64125
                             }  in
                           (uu____64123, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64109  in
                       FStar_All.pipe_left pos uu____64108
                   | uu____64162 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64248 = aux' true loc env1 p2  in
            (match uu____64248 with
             | (loc1,env2,var,p3,ans,uu____64292) ->
                 let uu____64307 =
                   FStar_List.fold_left
                     (fun uu____64356  ->
                        fun p4  ->
                          match uu____64356 with
                          | (loc2,env3,ps1) ->
                              let uu____64421 = aux' true loc2 env3 p4  in
                              (match uu____64421 with
                               | (loc3,env4,uu____64462,p5,ans1,uu____64465)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64307 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64626 ->
            let uu____64627 = aux' true loc env1 p1  in
            (match uu____64627 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64724 = aux_maybe_or env p  in
      match uu____64724 with
      | (env1,b,pats) ->
          ((let uu____64779 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64779
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
          let uu____64852 =
            let uu____64853 =
              let uu____64864 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64864, (ty, tacopt))  in
            LetBinder uu____64853  in
          (env, uu____64852, [])  in
        let op_to_ident x =
          let uu____64881 =
            let uu____64887 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64887, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64881  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64909 = op_to_ident x  in
              mklet uu____64909 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64911) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____64917;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____64933 = op_to_ident x  in
              let uu____64934 = desugar_term env t  in
              mklet uu____64933 uu____64934 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____64936);
                 FStar_Parser_AST.prange = uu____64937;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____64957 = desugar_term env t  in
              mklet x uu____64957 tacopt1
          | uu____64958 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____64971 = desugar_data_pat env p  in
           match uu____64971 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65000;
                      FStar_Syntax_Syntax.p = uu____65001;_},uu____65002)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65015;
                      FStar_Syntax_Syntax.p = uu____65016;_},uu____65017)::[]
                     -> []
                 | uu____65030 -> p1  in
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
  fun uu____65038  ->
    fun env  ->
      fun pat  ->
        let uu____65042 = desugar_data_pat env pat  in
        match uu____65042 with | (env1,uu____65058,pat1) -> (env1, pat1)

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
      let uu____65080 = desugar_term_aq env e  in
      match uu____65080 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65099 = desugar_typ_aq env e  in
      match uu____65099 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65109  ->
        fun range  ->
          match uu____65109 with
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
              ((let uu____65131 =
                  let uu____65133 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65133  in
                if uu____65131
                then
                  let uu____65136 =
                    let uu____65142 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65142)  in
                  FStar_Errors.log_issue range uu____65136
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
                  let uu____65163 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65163 range  in
                let lid1 =
                  let uu____65167 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65167 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65177 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65177 range  in
                           let private_fv =
                             let uu____65179 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65179 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65180 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65180.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65180.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65181 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65185 =
                        let uu____65191 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65191)
                         in
                      FStar_Errors.raise_error uu____65185 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65211 =
                  let uu____65218 =
                    let uu____65219 =
                      let uu____65236 =
                        let uu____65247 =
                          let uu____65256 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65256)  in
                        [uu____65247]  in
                      (lid1, uu____65236)  in
                    FStar_Syntax_Syntax.Tm_app uu____65219  in
                  FStar_Syntax_Syntax.mk uu____65218  in
                uu____65211 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65307 =
          let uu____65308 = unparen t  in uu____65308.FStar_Parser_AST.tm  in
        match uu____65307 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65309; FStar_Ident.ident = uu____65310;
              FStar_Ident.nsstr = uu____65311; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65316 ->
            let uu____65317 =
              let uu____65323 =
                let uu____65325 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65325  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65323)  in
            FStar_Errors.raise_error uu____65317 t.FStar_Parser_AST.range
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
          let uu___1725_65412 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65412.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65412.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65415 =
          let uu____65416 = unparen top  in uu____65416.FStar_Parser_AST.tm
           in
        match uu____65415 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65421 ->
            let uu____65430 = desugar_formula env top  in
            (uu____65430, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65439 = desugar_formula env t  in (uu____65439, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65448 = desugar_formula env t  in (uu____65448, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65475 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65475, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65477 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65477, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65486 =
                let uu____65487 =
                  let uu____65494 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65494, args)  in
                FStar_Parser_AST.Op uu____65487  in
              FStar_Parser_AST.mk_term uu____65486 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65499 =
              let uu____65500 =
                let uu____65501 =
                  let uu____65508 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65508, [e])  in
                FStar_Parser_AST.Op uu____65501  in
              FStar_Parser_AST.mk_term uu____65500 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65499
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65520 = FStar_Ident.text_of_id op_star  in
             uu____65520 = "*") &&
              (let uu____65525 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65525 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65542;_},t1::t2::[])
                  when
                  let uu____65548 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65548 FStar_Option.isNone ->
                  let uu____65555 = flatten1 t1  in
                  FStar_List.append uu____65555 [t2]
              | uu____65558 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65563 = top  in
              let uu____65564 =
                let uu____65565 =
                  let uu____65576 =
                    FStar_List.map (fun _65587  -> FStar_Util.Inr _65587)
                      terms
                     in
                  (uu____65576, rhs)  in
                FStar_Parser_AST.Sum uu____65565  in
              {
                FStar_Parser_AST.tm = uu____65564;
                FStar_Parser_AST.range =
                  (uu___1773_65563.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65563.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65595 =
              let uu____65596 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65596  in
            (uu____65595, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65602 =
              let uu____65608 =
                let uu____65610 =
                  let uu____65612 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65612 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65610  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65608)
               in
            FStar_Errors.raise_error uu____65602 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65627 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65627 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65634 =
                   let uu____65640 =
                     let uu____65642 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65642
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65640)
                    in
                 FStar_Errors.raise_error uu____65634
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65657 =
                     let uu____65682 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65744 = desugar_term_aq env t  in
                               match uu____65744 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65682 FStar_List.unzip  in
                   (match uu____65657 with
                    | (args1,aqs) ->
                        let uu____65877 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65877, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65894)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65911 =
              let uu___1802_65912 = top  in
              let uu____65913 =
                let uu____65914 =
                  let uu____65921 =
                    let uu___1804_65922 = top  in
                    let uu____65923 =
                      let uu____65924 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____65924  in
                    {
                      FStar_Parser_AST.tm = uu____65923;
                      FStar_Parser_AST.range =
                        (uu___1804_65922.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_65922.FStar_Parser_AST.level)
                    }  in
                  (uu____65921, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65914  in
              {
                FStar_Parser_AST.tm = uu____65913;
                FStar_Parser_AST.range =
                  (uu___1802_65912.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65912.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65911
        | FStar_Parser_AST.Construct (n1,(a,uu____65932)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____65952 =
                let uu___1814_65953 = top  in
                let uu____65954 =
                  let uu____65955 =
                    let uu____65962 =
                      let uu___1816_65963 = top  in
                      let uu____65964 =
                        let uu____65965 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____65965  in
                      {
                        FStar_Parser_AST.tm = uu____65964;
                        FStar_Parser_AST.range =
                          (uu___1816_65963.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_65963.FStar_Parser_AST.level)
                      }  in
                    (uu____65962, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____65955  in
                {
                  FStar_Parser_AST.tm = uu____65954;
                  FStar_Parser_AST.range =
                    (uu___1814_65953.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_65953.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____65952))
        | FStar_Parser_AST.Construct (n1,(a,uu____65973)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____65990 =
              let uu___1825_65991 = top  in
              let uu____65992 =
                let uu____65993 =
                  let uu____66000 =
                    let uu___1827_66001 = top  in
                    let uu____66002 =
                      let uu____66003 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66003  in
                    {
                      FStar_Parser_AST.tm = uu____66002;
                      FStar_Parser_AST.range =
                        (uu___1827_66001.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66001.FStar_Parser_AST.level)
                    }  in
                  (uu____66000, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65993  in
              {
                FStar_Parser_AST.tm = uu____65992;
                FStar_Parser_AST.range =
                  (uu___1825_65991.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_65991.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65990
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66009; FStar_Ident.ident = uu____66010;
              FStar_Ident.nsstr = uu____66011; FStar_Ident.str = "Type0";_}
            ->
            let uu____66016 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66016, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66017; FStar_Ident.ident = uu____66018;
              FStar_Ident.nsstr = uu____66019; FStar_Ident.str = "Type";_}
            ->
            let uu____66024 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66024, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66025; FStar_Ident.ident = uu____66026;
               FStar_Ident.nsstr = uu____66027; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66047 =
              let uu____66048 =
                let uu____66049 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66049  in
              mk1 uu____66048  in
            (uu____66047, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66050; FStar_Ident.ident = uu____66051;
              FStar_Ident.nsstr = uu____66052; FStar_Ident.str = "Effect";_}
            ->
            let uu____66057 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66057, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66058; FStar_Ident.ident = uu____66059;
              FStar_Ident.nsstr = uu____66060; FStar_Ident.str = "True";_}
            ->
            let uu____66065 =
              let uu____66066 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66066
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66065, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66067; FStar_Ident.ident = uu____66068;
              FStar_Ident.nsstr = uu____66069; FStar_Ident.str = "False";_}
            ->
            let uu____66074 =
              let uu____66075 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66075
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66074, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66078;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66081 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66081 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66090 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66090, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66092 =
                    let uu____66094 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66094 txt
                     in
                  failwith uu____66092))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66103 = desugar_name mk1 setpos env true l  in
              (uu____66103, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66112 = desugar_name mk1 setpos env true l  in
              (uu____66112, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66130 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66130 with
                | FStar_Pervasives_Native.Some uu____66140 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66148 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66148 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66166 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66187 =
                    let uu____66188 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66188  in
                  (uu____66187, noaqs)
              | uu____66194 ->
                  let uu____66202 =
                    let uu____66208 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66208)  in
                  FStar_Errors.raise_error uu____66202
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66218 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66218 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66225 =
                    let uu____66231 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66231)
                     in
                  FStar_Errors.raise_error uu____66225
                    top.FStar_Parser_AST.range
              | uu____66239 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66243 = desugar_name mk1 setpos env true lid'  in
                  (uu____66243, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66265 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66265 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66284 ->
                       let uu____66291 =
                         FStar_Util.take
                           (fun uu____66315  ->
                              match uu____66315 with
                              | (uu____66321,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66291 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66366 =
                              let uu____66391 =
                                FStar_List.map
                                  (fun uu____66434  ->
                                     match uu____66434 with
                                     | (t,imp) ->
                                         let uu____66451 =
                                           desugar_term_aq env t  in
                                         (match uu____66451 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66391
                                FStar_List.unzip
                               in
                            (match uu____66366 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66594 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66594, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66613 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66613 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66624 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66652  ->
                 match uu___437_66652 with
                 | FStar_Util.Inr uu____66658 -> true
                 | uu____66660 -> false) binders
            ->
            let terms =
              let uu____66669 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66686  ->
                        match uu___438_66686 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66692 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66669 [t]  in
            let uu____66694 =
              let uu____66719 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66776 = desugar_typ_aq env t1  in
                        match uu____66776 with
                        | (t',aq) ->
                            let uu____66787 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66787, aq)))
                 in
              FStar_All.pipe_right uu____66719 FStar_List.unzip  in
            (match uu____66694 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66897 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66897
                    in
                 let uu____66906 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66906, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____66933 =
              let uu____66950 =
                let uu____66957 =
                  let uu____66964 =
                    FStar_All.pipe_left
                      (fun _66973  -> FStar_Util.Inl _66973)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____66964]  in
                FStar_List.append binders uu____66957  in
              FStar_List.fold_left
                (fun uu____67018  ->
                   fun b  ->
                     match uu____67018 with
                     | (env1,tparams,typs) ->
                         let uu____67079 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67094 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67094)
                            in
                         (match uu____67079 with
                          | (xopt,t1) ->
                              let uu____67119 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67128 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67128)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67119 with
                               | (env2,x) ->
                                   let uu____67148 =
                                     let uu____67151 =
                                       let uu____67154 =
                                         let uu____67155 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67155
                                          in
                                       [uu____67154]  in
                                     FStar_List.append typs uu____67151  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67181 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67181.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67181.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67148)))) (env, [], [])
                uu____66950
               in
            (match uu____66933 with
             | (env1,uu____67209,targs) ->
                 let tup =
                   let uu____67232 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67232
                    in
                 let uu____67233 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67233, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67252 = uncurry binders t  in
            (match uu____67252 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67296 =
                   match uu___439_67296 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67313 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67313
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67337 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67337 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67370 = aux env [] bs  in (uu____67370, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67379 = desugar_binder env b  in
            (match uu____67379 with
             | (FStar_Pervasives_Native.None ,uu____67390) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67405 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67405 with
                  | ((x,uu____67421),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67434 =
                        let uu____67435 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67435  in
                      (uu____67434, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67514 = FStar_Util.set_is_empty i  in
                    if uu____67514
                    then
                      let uu____67519 = FStar_Util.set_union acc set1  in
                      aux uu____67519 sets2
                    else
                      (let uu____67524 =
                         let uu____67525 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67525  in
                       FStar_Pervasives_Native.Some uu____67524)
                 in
              let uu____67528 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67528 sets  in
            ((let uu____67532 = check_disjoint bvss  in
              match uu____67532 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67536 =
                    let uu____67542 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67542)
                     in
                  let uu____67546 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67536 uu____67546);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67554 =
                FStar_List.fold_left
                  (fun uu____67574  ->
                     fun pat  ->
                       match uu____67574 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67600,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67610 =
                                  let uu____67613 = free_type_vars env1 t  in
                                  FStar_List.append uu____67613 ftvs  in
                                (env1, uu____67610)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67618,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67629 =
                                  let uu____67632 = free_type_vars env1 t  in
                                  let uu____67635 =
                                    let uu____67638 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67638 ftvs  in
                                  FStar_List.append uu____67632 uu____67635
                                   in
                                (env1, uu____67629)
                            | uu____67643 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67554 with
              | (uu____67652,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67664 =
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
                    FStar_List.append uu____67664 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67721 =
                    match uu___440_67721 with
                    | [] ->
                        let uu____67748 = desugar_term_aq env1 body  in
                        (match uu____67748 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67785 =
                                       let uu____67786 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67786
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67785
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
                             let uu____67855 =
                               let uu____67858 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67858  in
                             (uu____67855, aq))
                    | p::rest ->
                        let uu____67873 = desugar_binding_pat env1 p  in
                        (match uu____67873 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67907)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____67922 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____67931 =
                               match b with
                               | LetBinder uu____67972 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68041) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68095 =
                                           let uu____68104 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68104, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68095
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68166,uu____68167) ->
                                              let tup2 =
                                                let uu____68169 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68169
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68174 =
                                                  let uu____68181 =
                                                    let uu____68182 =
                                                      let uu____68199 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68202 =
                                                        let uu____68213 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68222 =
                                                          let uu____68233 =
                                                            let uu____68242 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68242
                                                             in
                                                          [uu____68233]  in
                                                        uu____68213 ::
                                                          uu____68222
                                                         in
                                                      (uu____68199,
                                                        uu____68202)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68182
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68181
                                                   in
                                                uu____68174
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68293 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68293
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68344,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68346,pats)) ->
                                              let tupn =
                                                let uu____68391 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68391
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68404 =
                                                  let uu____68405 =
                                                    let uu____68422 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68425 =
                                                      let uu____68436 =
                                                        let uu____68447 =
                                                          let uu____68456 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68456
                                                           in
                                                        [uu____68447]  in
                                                      FStar_List.append args
                                                        uu____68436
                                                       in
                                                    (uu____68422,
                                                      uu____68425)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68405
                                                   in
                                                mk1 uu____68404  in
                                              let p2 =
                                                let uu____68504 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68504
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68551 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____67931 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68645,uu____68646,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68668 =
                let uu____68669 = unparen e  in
                uu____68669.FStar_Parser_AST.tm  in
              match uu____68668 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68679 ->
                  let uu____68680 = desugar_term_aq env e  in
                  (match uu____68680 with
                   | (head1,aq) ->
                       let uu____68693 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68693, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68700 ->
            let rec aux args aqs e =
              let uu____68777 =
                let uu____68778 = unparen e  in
                uu____68778.FStar_Parser_AST.tm  in
              match uu____68777 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68796 = desugar_term_aq env t  in
                  (match uu____68796 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68844 ->
                  let uu____68845 = desugar_term_aq env e  in
                  (match uu____68845 with
                   | (head1,aq) ->
                       let uu____68866 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68866, (join_aqs (aq :: aqs))))
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
            let uu____68929 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____68929
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
            let uu____68981 = desugar_term_aq env t  in
            (match uu____68981 with
             | (tm,s) ->
                 let uu____68992 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____68992, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____68998 =
              let uu____69011 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69011 then desugar_typ_aq else desugar_term_aq  in
            uu____68998 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69070 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69213  ->
                        match uu____69213 with
                        | (attr_opt,(p,def)) ->
                            let uu____69271 = is_app_pattern p  in
                            if uu____69271
                            then
                              let uu____69304 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69304, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69387 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69387, def1)
                               | uu____69432 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69470);
                                           FStar_Parser_AST.prange =
                                             uu____69471;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69520 =
                                            let uu____69541 =
                                              let uu____69546 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69546  in
                                            (uu____69541, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69520, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69638) ->
                                        if top_level
                                        then
                                          let uu____69674 =
                                            let uu____69695 =
                                              let uu____69700 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69700  in
                                            (uu____69695, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69674, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69791 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69824 =
                FStar_List.fold_left
                  (fun uu____69897  ->
                     fun uu____69898  ->
                       match (uu____69897, uu____69898) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70006,uu____70007),uu____70008))
                           ->
                           let uu____70125 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70151 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70151 with
                                  | (env2,xx) ->
                                      let uu____70170 =
                                        let uu____70173 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70173 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70170))
                             | FStar_Util.Inr l ->
                                 let uu____70181 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70181, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70125 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69824 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70329 =
                    match uu____70329 with
                    | (attrs_opt,(uu____70365,args,result_t),def) ->
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
                                let uu____70453 = is_comp_type env1 t  in
                                if uu____70453
                                then
                                  ((let uu____70457 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70467 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70467))
                                       in
                                    match uu____70457 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70474 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70477 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70477))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70474
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
                          | uu____70488 ->
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
                              let uu____70503 =
                                let uu____70504 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70504
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70503
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
                  let uu____70585 = desugar_term_aq env' body  in
                  (match uu____70585 with
                   | (body1,aq) ->
                       let uu____70598 =
                         let uu____70601 =
                           let uu____70602 =
                             let uu____70616 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70616)  in
                           FStar_Syntax_Syntax.Tm_let uu____70602  in
                         FStar_All.pipe_left mk1 uu____70601  in
                       (uu____70598, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70691 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70691 with
              | (env1,binder,pat1) ->
                  let uu____70713 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70739 = desugar_term_aq env1 t2  in
                        (match uu____70739 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70753 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70753
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70754 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70754, aq))
                    | LocalBinder (x,uu____70787) ->
                        let uu____70788 = desugar_term_aq env1 t2  in
                        (match uu____70788 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70802;
                                    FStar_Syntax_Syntax.p = uu____70803;_},uu____70804)::[]
                                   -> body1
                               | uu____70817 ->
                                   let uu____70820 =
                                     let uu____70827 =
                                       let uu____70828 =
                                         let uu____70851 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70854 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70851, uu____70854)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70828
                                        in
                                     FStar_Syntax_Syntax.mk uu____70827  in
                                   uu____70820 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70894 =
                               let uu____70897 =
                                 let uu____70898 =
                                   let uu____70912 =
                                     let uu____70915 =
                                       let uu____70916 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70916]  in
                                     FStar_Syntax_Subst.close uu____70915
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70912)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70898  in
                               FStar_All.pipe_left mk1 uu____70897  in
                             (uu____70894, aq))
                     in
                  (match uu____70713 with | (tm,aq) -> (tm, aq))
               in
            let uu____70978 = FStar_List.hd lbs  in
            (match uu____70978 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71022 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71022
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71038 =
                let uu____71039 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71039  in
              mk1 uu____71038  in
            let uu____71040 = desugar_term_aq env t1  in
            (match uu____71040 with
             | (t1',aq1) ->
                 let uu____71051 = desugar_term_aq env t2  in
                 (match uu____71051 with
                  | (t2',aq2) ->
                      let uu____71062 = desugar_term_aq env t3  in
                      (match uu____71062 with
                       | (t3',aq3) ->
                           let uu____71073 =
                             let uu____71074 =
                               let uu____71075 =
                                 let uu____71098 =
                                   let uu____71115 =
                                     let uu____71130 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71130,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71144 =
                                     let uu____71161 =
                                       let uu____71176 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71176,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71161]  in
                                   uu____71115 :: uu____71144  in
                                 (t1', uu____71098)  in
                               FStar_Syntax_Syntax.Tm_match uu____71075  in
                             mk1 uu____71074  in
                           (uu____71073, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71372 =
              match uu____71372 with
              | (pat,wopt,b) ->
                  let uu____71394 = desugar_match_pat env pat  in
                  (match uu____71394 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71425 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71425
                          in
                       let uu____71430 = desugar_term_aq env1 b  in
                       (match uu____71430 with
                        | (b1,aq) ->
                            let uu____71443 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71443, aq)))
               in
            let uu____71448 = desugar_term_aq env e  in
            (match uu____71448 with
             | (e1,aq) ->
                 let uu____71459 =
                   let uu____71490 =
                     let uu____71523 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71523 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71490
                     (fun uu____71741  ->
                        match uu____71741 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71459 with
                  | (brs,aqs) ->
                      let uu____71960 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____71960, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____71994 =
              let uu____72015 = is_comp_type env t  in
              if uu____72015
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72070 = desugar_term_aq env t  in
                 match uu____72070 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____71994 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72162 = desugar_term_aq env e  in
                 (match uu____72162 with
                  | (e1,aq) ->
                      let uu____72173 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72173, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72212,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72255 = FStar_List.hd fields  in
              match uu____72255 with | (f,uu____72267) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72313  ->
                        match uu____72313 with
                        | (g,uu____72320) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72327,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72341 =
                         let uu____72347 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72347)
                          in
                       FStar_Errors.raise_error uu____72341
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
                  let uu____72358 =
                    let uu____72369 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72400  ->
                              match uu____72400 with
                              | (f,uu____72410) ->
                                  let uu____72411 =
                                    let uu____72412 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72412
                                     in
                                  (uu____72411, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72369)  in
                  FStar_Parser_AST.Construct uu____72358
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72430 =
                      let uu____72431 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72431  in
                    FStar_Parser_AST.mk_term uu____72430
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72433 =
                      let uu____72446 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72476  ->
                                match uu____72476 with
                                | (f,uu____72486) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72446)  in
                    FStar_Parser_AST.Record uu____72433  in
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
            let uu____72546 = desugar_term_aq env recterm1  in
            (match uu____72546 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72562;
                         FStar_Syntax_Syntax.vars = uu____72563;_},args)
                      ->
                      let uu____72589 =
                        let uu____72590 =
                          let uu____72591 =
                            let uu____72608 =
                              let uu____72611 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72612 =
                                let uu____72615 =
                                  let uu____72616 =
                                    let uu____72623 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72623)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72616
                                   in
                                FStar_Pervasives_Native.Some uu____72615  in
                              FStar_Syntax_Syntax.fvar uu____72611
                                FStar_Syntax_Syntax.delta_constant
                                uu____72612
                               in
                            (uu____72608, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72591  in
                        FStar_All.pipe_left mk1 uu____72590  in
                      (uu____72589, s)
                  | uu____72652 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72656 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72656 with
              | (constrname,is_rec) ->
                  let uu____72675 = desugar_term_aq env e  in
                  (match uu____72675 with
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
                       let uu____72695 =
                         let uu____72696 =
                           let uu____72697 =
                             let uu____72714 =
                               let uu____72717 =
                                 let uu____72718 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72718
                                  in
                               FStar_Syntax_Syntax.fvar uu____72717
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72720 =
                               let uu____72731 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72731]  in
                             (uu____72714, uu____72720)  in
                           FStar_Syntax_Syntax.Tm_app uu____72697  in
                         FStar_All.pipe_left mk1 uu____72696  in
                       (uu____72695, s))))
        | FStar_Parser_AST.NamedTyp (uu____72768,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72778 =
              let uu____72779 = FStar_Syntax_Subst.compress tm  in
              uu____72779.FStar_Syntax_Syntax.n  in
            (match uu____72778 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72787 =
                   let uu___2520_72788 =
                     let uu____72789 =
                       let uu____72791 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72791  in
                     FStar_Syntax_Util.exp_string uu____72789  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72788.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72788.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72787, noaqs)
             | uu____72792 ->
                 let uu____72793 =
                   let uu____72799 =
                     let uu____72801 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72801
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72799)  in
                 FStar_Errors.raise_error uu____72793
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72810 = desugar_term_aq env e  in
            (match uu____72810 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72822 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72822, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72827 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72828 =
              let uu____72829 =
                let uu____72836 = desugar_term env e  in (bv, uu____72836)
                 in
              [uu____72829]  in
            (uu____72827, uu____72828)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72861 =
              let uu____72862 =
                let uu____72863 =
                  let uu____72870 = desugar_term env e  in (uu____72870, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72863  in
              FStar_All.pipe_left mk1 uu____72862  in
            (uu____72861, noaqs)
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
              let uu____72899 =
                let uu____72900 =
                  let uu____72907 =
                    let uu____72908 =
                      let uu____72909 =
                        let uu____72918 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____72931 =
                          let uu____72932 =
                            let uu____72933 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____72933  in
                          FStar_Parser_AST.mk_term uu____72932
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____72918, uu____72931,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72909  in
                    FStar_Parser_AST.mk_term uu____72908
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72907)  in
                FStar_Parser_AST.Abs uu____72900  in
              FStar_Parser_AST.mk_term uu____72899
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
                   fun uu____72979  ->
                     match uu____72979 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____72983 =
                           let uu____72990 =
                             let uu____72995 = eta_and_annot rel2  in
                             (uu____72995, FStar_Parser_AST.Nothing)  in
                           let uu____72996 =
                             let uu____73003 =
                               let uu____73010 =
                                 let uu____73015 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73015, FStar_Parser_AST.Nothing)  in
                               let uu____73016 =
                                 let uu____73023 =
                                   let uu____73028 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73028, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73023]  in
                               uu____73010 :: uu____73016  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73003
                              in
                           uu____72990 :: uu____72996  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____72983
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73050 =
                let uu____73057 =
                  let uu____73062 = FStar_Parser_AST.thunk e1  in
                  (uu____73062, FStar_Parser_AST.Nothing)  in
                [uu____73057]  in
              FStar_Parser_AST.mkApp finish1 uu____73050
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73071 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73072 = desugar_formula env top  in
            (uu____73072, noaqs)
        | uu____73073 ->
            let uu____73074 =
              let uu____73080 =
                let uu____73082 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73082  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73080)  in
            FStar_Errors.raise_error uu____73074 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73092 -> false
    | uu____73102 -> true

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
           (fun uu____73140  ->
              match uu____73140 with
              | (a,imp) ->
                  let uu____73153 = desugar_term env a  in
                  arg_withimp_e imp uu____73153))

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
          let is_requires uu____73190 =
            match uu____73190 with
            | (t1,uu____73197) ->
                let uu____73198 =
                  let uu____73199 = unparen t1  in
                  uu____73199.FStar_Parser_AST.tm  in
                (match uu____73198 with
                 | FStar_Parser_AST.Requires uu____73201 -> true
                 | uu____73210 -> false)
             in
          let is_ensures uu____73222 =
            match uu____73222 with
            | (t1,uu____73229) ->
                let uu____73230 =
                  let uu____73231 = unparen t1  in
                  uu____73231.FStar_Parser_AST.tm  in
                (match uu____73230 with
                 | FStar_Parser_AST.Ensures uu____73233 -> true
                 | uu____73242 -> false)
             in
          let is_app head1 uu____73260 =
            match uu____73260 with
            | (t1,uu____73268) ->
                let uu____73269 =
                  let uu____73270 = unparen t1  in
                  uu____73270.FStar_Parser_AST.tm  in
                (match uu____73269 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73273;
                        FStar_Parser_AST.level = uu____73274;_},uu____73275,uu____73276)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73278 -> false)
             in
          let is_smt_pat uu____73290 =
            match uu____73290 with
            | (t1,uu____73297) ->
                let uu____73298 =
                  let uu____73299 = unparen t1  in
                  uu____73299.FStar_Parser_AST.tm  in
                (match uu____73298 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73303);
                               FStar_Parser_AST.range = uu____73304;
                               FStar_Parser_AST.level = uu____73305;_},uu____73306)::uu____73307::[])
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
                               FStar_Parser_AST.range = uu____73356;
                               FStar_Parser_AST.level = uu____73357;_},uu____73358)::uu____73359::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73392 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73427 = head_and_args t1  in
            match uu____73427 with
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
                     let thunk_ens uu____73520 =
                       match uu____73520 with
                       | (e,i) ->
                           let uu____73531 = FStar_Parser_AST.thunk e  in
                           (uu____73531, i)
                        in
                     let fail_lemma uu____73543 =
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
                           let uu____73649 =
                             let uu____73656 =
                               let uu____73663 = thunk_ens ens  in
                               [uu____73663; nil_pat]  in
                             req_true :: uu____73656  in
                           unit_tm :: uu____73649
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73710 =
                             let uu____73717 =
                               let uu____73724 = thunk_ens ens  in
                               [uu____73724; nil_pat]  in
                             req :: uu____73717  in
                           unit_tm :: uu____73710
                       | ens::smtpat::[] when
                           (((let uu____73773 = is_requires ens  in
                              Prims.op_Negation uu____73773) &&
                               (let uu____73776 = is_smt_pat ens  in
                                Prims.op_Negation uu____73776))
                              &&
                              (let uu____73779 = is_decreases ens  in
                               Prims.op_Negation uu____73779))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73781 =
                             let uu____73788 =
                               let uu____73795 = thunk_ens ens  in
                               [uu____73795; smtpat]  in
                             req_true :: uu____73788  in
                           unit_tm :: uu____73781
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73842 =
                             let uu____73849 =
                               let uu____73856 = thunk_ens ens  in
                               [uu____73856; nil_pat; dec]  in
                             req_true :: uu____73849  in
                           unit_tm :: uu____73842
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73916 =
                             let uu____73923 =
                               let uu____73930 = thunk_ens ens  in
                               [uu____73930; smtpat; dec]  in
                             req_true :: uu____73923  in
                           unit_tm :: uu____73916
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____73990 =
                             let uu____73997 =
                               let uu____74004 = thunk_ens ens  in
                               [uu____74004; nil_pat; dec]  in
                             req :: uu____73997  in
                           unit_tm :: uu____73990
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74064 =
                             let uu____74071 =
                               let uu____74078 = thunk_ens ens  in
                               [uu____74078; smtpat]  in
                             req :: uu____74071  in
                           unit_tm :: uu____74064
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74143 =
                             let uu____74150 =
                               let uu____74157 = thunk_ens ens  in
                               [uu____74157; dec; smtpat]  in
                             req :: uu____74150  in
                           unit_tm :: uu____74143
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74219 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74219, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74247 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74247
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74250 =
                       let uu____74257 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74257, [])  in
                     (uu____74250, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74275 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74275
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74278 =
                       let uu____74285 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74285, [])  in
                     (uu____74278, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74307 =
                       let uu____74314 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74314, [])  in
                     (uu____74307, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74337 when allow_type_promotion ->
                     let default_effect =
                       let uu____74339 = FStar_Options.ml_ish ()  in
                       if uu____74339
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74345 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74345
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74352 =
                       let uu____74359 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74359, [])  in
                     (uu____74352, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74382 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74401 = pre_process_comp_typ t  in
          match uu____74401 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74453 =
                    let uu____74459 =
                      let uu____74461 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74461
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74459)
                     in
                  fail1 uu____74453)
               else ();
               (let is_universe uu____74477 =
                  match uu____74477 with
                  | (uu____74483,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74485 = FStar_Util.take is_universe args  in
                match uu____74485 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74544  ->
                           match uu____74544 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74551 =
                      let uu____74566 = FStar_List.hd args1  in
                      let uu____74575 = FStar_List.tl args1  in
                      (uu____74566, uu____74575)  in
                    (match uu____74551 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74630 =
                           let is_decrease uu____74669 =
                             match uu____74669 with
                             | (t1,uu____74680) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74691;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74692;_},uu____74693::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74732 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74630 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74849  ->
                                        match uu____74849 with
                                        | (t1,uu____74859) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74868,(arg,uu____74870)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74909 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____74930 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____74942 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____74942
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____74949 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____74949
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____74959 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____74959
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____74966 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____74966
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____74973 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____74973
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____74980 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____74980
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75001 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75001
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
                                                    let uu____75092 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75092
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
                                              | uu____75113 -> pat  in
                                            let uu____75114 =
                                              let uu____75125 =
                                                let uu____75136 =
                                                  let uu____75145 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75145, aq)  in
                                                [uu____75136]  in
                                              ens :: uu____75125  in
                                            req :: uu____75114
                                        | uu____75186 -> rest2
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
        | uu____75218 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75240 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75240.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75240.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75282 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75282.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75282.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75282.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75345 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75345)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75358 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75358 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75368 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75368.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75368.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75394 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75408 =
                     let uu____75411 =
                       let uu____75412 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75412]  in
                     no_annot_abs uu____75411 body2  in
                   FStar_All.pipe_left setpos uu____75408  in
                 let uu____75433 =
                   let uu____75434 =
                     let uu____75451 =
                       let uu____75454 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75454
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75456 =
                       let uu____75467 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75467]  in
                     (uu____75451, uu____75456)  in
                   FStar_Syntax_Syntax.Tm_app uu____75434  in
                 FStar_All.pipe_left mk1 uu____75433)
        | uu____75506 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75587 = q (rest, pats, body)  in
              let uu____75594 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75587 uu____75594
                FStar_Parser_AST.Formula
               in
            let uu____75595 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75595 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75604 -> failwith "impossible"  in
      let uu____75608 =
        let uu____75609 = unparen f  in uu____75609.FStar_Parser_AST.tm  in
      match uu____75608 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75622,uu____75623) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75635,uu____75636) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75668 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75668
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75704 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75704
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75748 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75753 =
        FStar_List.fold_left
          (fun uu____75786  ->
             fun b  ->
               match uu____75786 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75830 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75830.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75830.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75830.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75845 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75845 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75863 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75863.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75863.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75864 =
                               let uu____75871 =
                                 let uu____75876 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75876)  in
                               uu____75871 :: out  in
                             (env2, uu____75864))
                    | uu____75887 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75753 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____75960 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____75960)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____75965 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____75965)
      | FStar_Parser_AST.TVariable x ->
          let uu____75969 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____75969)
      | FStar_Parser_AST.NoName t ->
          let uu____75973 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____75973)
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
      fun uu___441_75981  ->
        match uu___441_75981 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76003 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76003, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76020 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76020 with
             | (env1,a1) ->
                 let uu____76037 =
                   let uu____76044 = trans_aqual env1 imp  in
                   ((let uu___2962_76050 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76050.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76050.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76044)
                    in
                 (uu____76037, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76058  ->
      match uu___442_76058 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76062 =
            let uu____76063 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76063  in
          FStar_Pervasives_Native.Some uu____76062
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76079) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76081) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76084 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76102 = binder_ident b  in
         FStar_Common.list_of_option uu____76102) bs
  
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
               (fun uu___443_76139  ->
                  match uu___443_76139 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76144 -> false))
           in
        let quals2 q =
          let uu____76158 =
            (let uu____76162 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76162) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76158
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76179 = FStar_Ident.range_of_lid disc_name  in
                let uu____76180 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76179;
                  FStar_Syntax_Syntax.sigquals = uu____76180;
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
            let uu____76220 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76258  ->
                        match uu____76258 with
                        | (x,uu____76269) ->
                            let uu____76274 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76274 with
                             | (field_name,uu____76282) ->
                                 let only_decl =
                                   ((let uu____76287 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76287)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76289 =
                                        let uu____76291 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76291.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76289)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76309 =
                                       FStar_List.filter
                                         (fun uu___444_76313  ->
                                            match uu___444_76313 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76316 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76309
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76331  ->
                                             match uu___445_76331 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76336 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76339 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76339;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76346 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76346
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76357 =
                                        let uu____76362 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76362  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76357;
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
                                      let uu____76366 =
                                        let uu____76367 =
                                          let uu____76374 =
                                            let uu____76377 =
                                              let uu____76378 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76378
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76377]  in
                                          ((false, [lb]), uu____76374)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76367
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76366;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76220 FStar_List.flatten
  
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
            (lid,uu____76427,t,uu____76429,n1,uu____76431) when
            let uu____76438 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76438 ->
            let uu____76440 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76440 with
             | (formals,uu____76458) ->
                 (match formals with
                  | [] -> []
                  | uu____76487 ->
                      let filter_records uu___446_76503 =
                        match uu___446_76503 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76506,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76518 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76520 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76520 with
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
                      let uu____76532 = FStar_Util.first_N n1 formals  in
                      (match uu____76532 with
                       | (uu____76561,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76595 -> []
  
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
                    let uu____76674 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76674
                    then
                      let uu____76680 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76680
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76684 =
                      let uu____76689 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76689  in
                    let uu____76690 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76696 =
                          let uu____76699 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76699  in
                        FStar_Syntax_Util.arrow typars uu____76696
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76704 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76684;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76690;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76704;
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
          let tycon_id uu___447_76758 =
            match uu___447_76758 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76760,uu____76761) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76771,uu____76772,uu____76773) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76783,uu____76784,uu____76785) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76815,uu____76816,uu____76817) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76863) ->
                let uu____76864 =
                  let uu____76865 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76865  in
                FStar_Parser_AST.mk_term uu____76864 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76867 =
                  let uu____76868 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76868  in
                FStar_Parser_AST.mk_term uu____76867 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76870) ->
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
              | uu____76901 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76909 =
                     let uu____76910 =
                       let uu____76917 = binder_to_term b  in
                       (out, uu____76917, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76910  in
                   FStar_Parser_AST.mk_term uu____76909
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_76929 =
            match uu___448_76929 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____76986  ->
                       match uu____76986 with
                       | (x,t,uu____76997) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77003 =
                    let uu____77004 =
                      let uu____77005 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77005  in
                    FStar_Parser_AST.mk_term uu____77004
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77003 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77012 = binder_idents parms  in id1 ::
                    uu____77012
                   in
                (FStar_List.iter
                   (fun uu____77030  ->
                      match uu____77030 with
                      | (f,uu____77040,uu____77041) ->
                          let uu____77046 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77046
                          then
                            let uu____77051 =
                              let uu____77057 =
                                let uu____77059 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77059
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77057)
                               in
                            FStar_Errors.raise_error uu____77051
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77065 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77092  ->
                            match uu____77092 with
                            | (x,uu____77102,uu____77103) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77065)))
            | uu____77161 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77201 =
            match uu___449_77201 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77225 = typars_of_binders _env binders  in
                (match uu____77225 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77261 =
                         let uu____77262 =
                           let uu____77263 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77263  in
                         FStar_Parser_AST.mk_term uu____77262
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77261 binders  in
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
            | uu____77274 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77317 =
              FStar_List.fold_left
                (fun uu____77351  ->
                   fun uu____77352  ->
                     match (uu____77351, uu____77352) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77421 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77421 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77317 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77512 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77512
                | uu____77513 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77521 = desugar_abstract_tc quals env [] tc  in
              (match uu____77521 with
               | (uu____77534,uu____77535,se,uu____77537) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77540,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77559 =
                                 let uu____77561 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77561  in
                               if uu____77559
                               then
                                 let uu____77564 =
                                   let uu____77570 =
                                     let uu____77572 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77572
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77570)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77564
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
                           | uu____77585 ->
                               let uu____77586 =
                                 let uu____77593 =
                                   let uu____77594 =
                                     let uu____77609 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77609)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77594
                                    in
                                 FStar_Syntax_Syntax.mk uu____77593  in
                               uu____77586 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77625 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77625.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77625.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77625.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77626 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77630 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77630
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77643 = typars_of_binders env binders  in
              (match uu____77643 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77677 =
                           FStar_Util.for_some
                             (fun uu___450_77680  ->
                                match uu___450_77680 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77683 -> false) quals
                            in
                         if uu____77677
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77691 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77691
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77696 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77702  ->
                               match uu___451_77702 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77705 -> false))
                        in
                     if uu____77696
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77719 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77719
                     then
                       let uu____77725 =
                         let uu____77732 =
                           let uu____77733 = unparen t  in
                           uu____77733.FStar_Parser_AST.tm  in
                         match uu____77732 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77754 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77784)::args_rev ->
                                   let uu____77796 =
                                     let uu____77797 = unparen last_arg  in
                                     uu____77797.FStar_Parser_AST.tm  in
                                   (match uu____77796 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77825 -> ([], args))
                               | uu____77834 -> ([], args)  in
                             (match uu____77754 with
                              | (cattributes,args1) ->
                                  let uu____77873 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77873))
                         | uu____77884 -> (t, [])  in
                       match uu____77725 with
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
                                  (fun uu___452_77907  ->
                                     match uu___452_77907 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77910 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____77919)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____77943 = tycon_record_as_variant trec  in
              (match uu____77943 with
               | (t,fs) ->
                   let uu____77960 =
                     let uu____77963 =
                       let uu____77964 =
                         let uu____77973 =
                           let uu____77976 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____77976  in
                         (uu____77973, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____77964  in
                     uu____77963 :: quals  in
                   desugar_tycon env d uu____77960 [t])
          | uu____77981::uu____77982 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78152 = et  in
                match uu____78152 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78382 ->
                         let trec = tc  in
                         let uu____78406 = tycon_record_as_variant trec  in
                         (match uu____78406 with
                          | (t,fs) ->
                              let uu____78466 =
                                let uu____78469 =
                                  let uu____78470 =
                                    let uu____78479 =
                                      let uu____78482 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78482  in
                                    (uu____78479, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78470
                                   in
                                uu____78469 :: quals1  in
                              collect_tcs uu____78466 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78572 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78572 with
                          | (env2,uu____78633,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78786 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78786 with
                          | (env2,uu____78847,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____78975 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79025 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79025 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79540  ->
                             match uu___454_79540 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79606,uu____79607);
                                    FStar_Syntax_Syntax.sigrng = uu____79608;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79609;
                                    FStar_Syntax_Syntax.sigmeta = uu____79610;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79611;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79675 =
                                     typars_of_binders env1 binders  in
                                   match uu____79675 with
                                   | (env2,tpars1) ->
                                       let uu____79702 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79702 with
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
                                 let uu____79731 =
                                   let uu____79750 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79750)
                                    in
                                 [uu____79731]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79810);
                                    FStar_Syntax_Syntax.sigrng = uu____79811;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79813;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79814;_},constrs,tconstr,quals1)
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
                                 let uu____79915 = push_tparams env1 tpars
                                    in
                                 (match uu____79915 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____79982  ->
                                             match uu____79982 with
                                             | (x,uu____79994) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____79999 =
                                        let uu____80026 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80136  ->
                                                  match uu____80136 with
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
                                                        let uu____80196 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80196
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
                                                                uu___453_80207
                                                                 ->
                                                                match uu___453_80207
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80219
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80227 =
                                                        let uu____80246 =
                                                          let uu____80247 =
                                                            let uu____80248 =
                                                              let uu____80264
                                                                =
                                                                let uu____80265
                                                                  =
                                                                  let uu____80268
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80268
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80265
                                                                 in
                                                              (name, univs1,
                                                                uu____80264,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80248
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80247;
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
                                                          uu____80246)
                                                         in
                                                      (name, uu____80227)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80026
                                         in
                                      (match uu____79999 with
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
                             | uu____80484 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80612  ->
                             match uu____80612 with
                             | (name_doc,uu____80638,uu____80639) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80711  ->
                             match uu____80711 with
                             | (uu____80730,uu____80731,se) -> se))
                      in
                   let uu____80757 =
                     let uu____80764 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80764 rng
                      in
                   (match uu____80757 with
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
                               (fun uu____80826  ->
                                  match uu____80826 with
                                  | (uu____80847,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80895,tps,k,uu____80898,constrs)
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
                                      let uu____80919 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____80934 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____80951,uu____80952,uu____80953,uu____80954,uu____80955)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____80962
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____80934
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____80966 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_80973 
                                                          ->
                                                          match uu___455_80973
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____80975 ->
                                                              true
                                                          | uu____80985 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____80966))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____80919
                                  | uu____80987 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81004  ->
                                 match uu____81004 with
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
      let uu____81049 =
        FStar_List.fold_left
          (fun uu____81084  ->
             fun b  ->
               match uu____81084 with
               | (env1,binders1) ->
                   let uu____81128 = desugar_binder env1 b  in
                   (match uu____81128 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81151 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81151 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81204 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81049 with
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
          let uu____81308 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81315  ->
                    match uu___456_81315 with
                    | FStar_Syntax_Syntax.Reflectable uu____81317 -> true
                    | uu____81319 -> false))
             in
          if uu____81308
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81324 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81324
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
      let uu____81365 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81365 with
      | (hd1,args) ->
          let uu____81418 =
            let uu____81433 =
              let uu____81434 = FStar_Syntax_Subst.compress hd1  in
              uu____81434.FStar_Syntax_Syntax.n  in
            (uu____81433, args)  in
          (match uu____81418 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81459)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81494 =
                 let uu____81499 =
                   let uu____81508 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81508 a1  in
                 uu____81499 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81494 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81538 =
                      let uu____81547 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81547, b)  in
                    FStar_Pervasives_Native.Some uu____81538
                | uu____81564 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81618) when
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
           | uu____81653 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81825 = desugar_binders monad_env eff_binders  in
                  match uu____81825 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81865 =
                          let uu____81867 =
                            let uu____81876 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81876  in
                          FStar_List.length uu____81867  in
                        uu____81865 = (Prims.parse_int "1")  in
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
                            (uu____81960,uu____81961,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____81963,uu____81964,uu____81965),uu____81966)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82003 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82006 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82018 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82018 mandatory_members)
                          eff_decls
                         in
                      (match uu____82006 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82037 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82066  ->
                                     fun decl  ->
                                       match uu____82066 with
                                       | (env2,out) ->
                                           let uu____82086 =
                                             desugar_decl env2 decl  in
                                           (match uu____82086 with
                                            | (env3,ses) ->
                                                let uu____82099 =
                                                  let uu____82102 =
                                                    FStar_List.hd ses  in
                                                  uu____82102 :: out  in
                                                (env3, uu____82099)))
                                  (env1, []))
                              in
                           (match uu____82037 with
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
                                              (uu____82171,uu____82172,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82175,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82176,(def,uu____82178)::
                                                      (cps_type,uu____82180)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82181;
                                                   FStar_Parser_AST.level =
                                                     uu____82182;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82238 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82238 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82276 =
                                                     let uu____82277 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82278 =
                                                       let uu____82279 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82279
                                                        in
                                                     let uu____82286 =
                                                       let uu____82287 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82287
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82277;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82278;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82286
                                                     }  in
                                                   (uu____82276, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82296,uu____82297,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82300,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82339 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82339 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82377 =
                                                     let uu____82378 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82379 =
                                                       let uu____82380 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82380
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82378;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82379;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82377, doc1))
                                          | uu____82389 ->
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
                                    let uu____82425 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82425
                                     in
                                  let uu____82427 =
                                    let uu____82428 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82428
                                     in
                                  ([], uu____82427)  in
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
                                      let uu____82446 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82446)  in
                                    let uu____82453 =
                                      let uu____82454 =
                                        let uu____82455 =
                                          let uu____82456 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82456
                                           in
                                        let uu____82466 = lookup1 "return"
                                           in
                                        let uu____82468 = lookup1 "bind"  in
                                        let uu____82470 =
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
                                            uu____82455;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82466;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82468;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82470
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82454
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82453;
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
                                         (fun uu___457_82478  ->
                                            match uu___457_82478 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82481 -> true
                                            | uu____82483 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82498 =
                                       let uu____82499 =
                                         let uu____82500 =
                                           lookup1 "return_wp"  in
                                         let uu____82502 = lookup1 "bind_wp"
                                            in
                                         let uu____82504 =
                                           lookup1 "if_then_else"  in
                                         let uu____82506 = lookup1 "ite_wp"
                                            in
                                         let uu____82508 = lookup1 "stronger"
                                            in
                                         let uu____82510 = lookup1 "close_wp"
                                            in
                                         let uu____82512 = lookup1 "assert_p"
                                            in
                                         let uu____82514 = lookup1 "assume_p"
                                            in
                                         let uu____82516 = lookup1 "null_wp"
                                            in
                                         let uu____82518 = lookup1 "trivial"
                                            in
                                         let uu____82520 =
                                           if rr
                                           then
                                             let uu____82522 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82522
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82540 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82545 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82550 =
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
                                             uu____82500;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82502;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82504;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82506;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82508;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82510;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82512;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82514;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82516;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82518;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82520;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82540;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82545;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82550
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82499
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82498;
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
                                          fun uu____82576  ->
                                            match uu____82576 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82590 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82590
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
                let uu____82614 = desugar_binders env1 eff_binders  in
                match uu____82614 with
                | (env2,binders) ->
                    let uu____82651 =
                      let uu____82662 = head_and_args defn  in
                      match uu____82662 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82699 ->
                                let uu____82700 =
                                  let uu____82706 =
                                    let uu____82708 =
                                      let uu____82710 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82710 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82708  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82706)
                                   in
                                FStar_Errors.raise_error uu____82700
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82716 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82746)::args_rev ->
                                let uu____82758 =
                                  let uu____82759 = unparen last_arg  in
                                  uu____82759.FStar_Parser_AST.tm  in
                                (match uu____82758 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82787 -> ([], args))
                            | uu____82796 -> ([], args)  in
                          (match uu____82716 with
                           | (cattributes,args1) ->
                               let uu____82839 = desugar_args env2 args1  in
                               let uu____82840 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82839, uu____82840))
                       in
                    (match uu____82651 with
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
                          (let uu____82880 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82880 with
                           | (ed_binders,uu____82894,ed_binders_opening) ->
                               let sub' shift_n uu____82913 =
                                 match uu____82913 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____82928 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____82928 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____82932 =
                                       let uu____82933 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____82933)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____82932
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____82954 =
                                   let uu____82955 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____82955
                                    in
                                 let uu____82970 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____82971 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____82972 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____82973 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____82974 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____82975 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____82976 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____82977 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____82978 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____82979 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____82980 =
                                   let uu____82981 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____82981
                                    in
                                 let uu____82996 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____82997 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____82998 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83014 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83015 =
                                          let uu____83016 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83016
                                           in
                                        let uu____83037 =
                                          let uu____83038 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83038
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83014;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83015;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83037
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
                                     uu____82954;
                                   FStar_Syntax_Syntax.ret_wp = uu____82970;
                                   FStar_Syntax_Syntax.bind_wp = uu____82971;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____82972;
                                   FStar_Syntax_Syntax.ite_wp = uu____82973;
                                   FStar_Syntax_Syntax.stronger = uu____82974;
                                   FStar_Syntax_Syntax.close_wp = uu____82975;
                                   FStar_Syntax_Syntax.assert_p = uu____82976;
                                   FStar_Syntax_Syntax.assume_p = uu____82977;
                                   FStar_Syntax_Syntax.null_wp = uu____82978;
                                   FStar_Syntax_Syntax.trivial = uu____82979;
                                   FStar_Syntax_Syntax.repr = uu____82980;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____82996;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____82997;
                                   FStar_Syntax_Syntax.actions = uu____82998;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83062 =
                                     let uu____83064 =
                                       let uu____83073 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83073
                                        in
                                     FStar_List.length uu____83064  in
                                   uu____83062 = (Prims.parse_int "1")  in
                                 let uu____83106 =
                                   let uu____83109 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83109 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____83106;
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
                                             let uu____83133 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83133
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83135 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83135
                                 then
                                   let reflect_lid =
                                     let uu____83142 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83142
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
    let uu____83154 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83154 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83239 ->
              let uu____83242 =
                let uu____83244 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83244
                 in
              Prims.op_Hat "\n  " uu____83242
          | uu____83247 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83266  ->
               match uu____83266 with
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
          let uu____83311 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83311
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83314 =
          let uu____83325 = FStar_Syntax_Syntax.as_arg arg  in [uu____83325]
           in
        FStar_Syntax_Util.mk_app fv uu____83314

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83356 = desugar_decl_noattrs env d  in
      match uu____83356 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83374 = mk_comment_attr d  in uu____83374 :: attrs1  in
          let uu____83375 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83385 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83385.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83385.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83385.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83385.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83388 = sigelt  in
                      let uu____83389 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83395 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83395) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83388.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83388.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83388.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83388.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83389
                      })) sigelts
             in
          (env1, uu____83375)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83421 = desugar_decl_aux env d  in
      match uu____83421 with
      | (env1,ses) ->
          let uu____83432 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83432)

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
      | FStar_Parser_AST.Fsdoc uu____83460 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83465 = FStar_Syntax_DsEnv.iface env  in
          if uu____83465
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83480 =
               let uu____83482 =
                 let uu____83484 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83485 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83484
                   uu____83485
                  in
               Prims.op_Negation uu____83482  in
             if uu____83480
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83499 =
                  let uu____83501 =
                    let uu____83503 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83503 lid  in
                  Prims.op_Negation uu____83501  in
                if uu____83499
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83517 =
                     let uu____83519 =
                       let uu____83521 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83521
                         lid
                        in
                     Prims.op_Negation uu____83519  in
                   if uu____83517
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83539 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83539, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83580,uu____83581)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83620 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83647  ->
                 match uu____83647 with | (x,uu____83655) -> x) tcs
             in
          let uu____83660 =
            let uu____83665 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83665 tcs1  in
          (match uu____83660 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83682 =
                   let uu____83683 =
                     let uu____83690 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83690  in
                   [uu____83683]  in
                 let uu____83703 =
                   let uu____83706 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83709 =
                     let uu____83720 =
                       let uu____83729 =
                         let uu____83730 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83730  in
                       FStar_Syntax_Syntax.as_arg uu____83729  in
                     [uu____83720]  in
                   FStar_Syntax_Util.mk_app uu____83706 uu____83709  in
                 FStar_Syntax_Util.abs uu____83682 uu____83703
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83770,id1))::uu____83772 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83775::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83779 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83779 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83785 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83785]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83806) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83816,uu____83817,uu____83818,uu____83819,uu____83820)
                     ->
                     let uu____83829 =
                       let uu____83830 =
                         let uu____83831 =
                           let uu____83838 = mkclass lid  in
                           (meths, uu____83838)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83831  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83830;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83829]
                 | uu____83841 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83875;
                    FStar_Parser_AST.prange = uu____83876;_},uu____83877)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83887;
                    FStar_Parser_AST.prange = uu____83888;_},uu____83889)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83905;
                         FStar_Parser_AST.prange = uu____83906;_},uu____83907);
                    FStar_Parser_AST.prange = uu____83908;_},uu____83909)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____83931;
                         FStar_Parser_AST.prange = uu____83932;_},uu____83933);
                    FStar_Parser_AST.prange = uu____83934;_},uu____83935)::[]
                   -> false
               | (p,uu____83964)::[] ->
                   let uu____83973 = is_app_pattern p  in
                   Prims.op_Negation uu____83973
               | uu____83975 -> false)
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
            let uu____84050 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84050 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84063 =
                     let uu____84064 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84064.FStar_Syntax_Syntax.n  in
                   match uu____84063 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84074) ->
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
                         | uu____84110::uu____84111 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84114 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84130  ->
                                     match uu___458_84130 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84133;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84134;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84135;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84136;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84137;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84138;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84139;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84151;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84152;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84153;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84154;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84155;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84156;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84170 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84203  ->
                                   match uu____84203 with
                                   | (uu____84217,(uu____84218,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84170
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84238 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84238
                         then
                           let uu____84244 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84259 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84261 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84261.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84261.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84259.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84244)
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
                   | uu____84291 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84299 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84318 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84299 with
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
                       let uu___4019_84355 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84355.FStar_Parser_AST.prange)
                       }
                   | uu____84362 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84369 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84369.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84369.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84369.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84405 id1 =
                   match uu____84405 with
                   | (env1,ses) ->
                       let main =
                         let uu____84426 =
                           let uu____84427 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84427  in
                         FStar_Parser_AST.mk_term uu____84426
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
                       let uu____84477 = desugar_decl env1 id_decl  in
                       (match uu____84477 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84495 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84495 FStar_Util.set_elements
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
            let uu____84519 = close_fun env t  in
            desugar_term env uu____84519  in
          let quals1 =
            let uu____84523 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84523
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84535 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84535;
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
                let uu____84549 =
                  let uu____84558 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84558]  in
                let uu____84577 =
                  let uu____84580 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84580
                   in
                FStar_Syntax_Util.arrow uu____84549 uu____84577
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
            let uu____84635 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84635 with
            | FStar_Pervasives_Native.None  ->
                let uu____84638 =
                  let uu____84644 =
                    let uu____84646 =
                      let uu____84648 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84648 " not found"  in
                    Prims.op_Hat "Effect name " uu____84646  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84644)  in
                FStar_Errors.raise_error uu____84638
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84656 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84674 =
                  let uu____84677 =
                    let uu____84678 = desugar_term env t  in
                    ([], uu____84678)  in
                  FStar_Pervasives_Native.Some uu____84677  in
                (uu____84674, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84691 =
                  let uu____84694 =
                    let uu____84695 = desugar_term env wp  in
                    ([], uu____84695)  in
                  FStar_Pervasives_Native.Some uu____84694  in
                let uu____84702 =
                  let uu____84705 =
                    let uu____84706 = desugar_term env t  in
                    ([], uu____84706)  in
                  FStar_Pervasives_Native.Some uu____84705  in
                (uu____84691, uu____84702)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84718 =
                  let uu____84721 =
                    let uu____84722 = desugar_term env t  in
                    ([], uu____84722)  in
                  FStar_Pervasives_Native.Some uu____84721  in
                (FStar_Pervasives_Native.None, uu____84718)
             in
          (match uu____84656 with
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
            let uu____84756 =
              let uu____84757 =
                let uu____84764 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84764, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84757  in
            {
              FStar_Syntax_Syntax.sigel = uu____84756;
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
      let uu____84791 =
        FStar_List.fold_left
          (fun uu____84811  ->
             fun d  ->
               match uu____84811 with
               | (env1,sigelts) ->
                   let uu____84831 = desugar_decl env1 d  in
                   (match uu____84831 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84791 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84876 =
            match uu___460_84876 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84890,FStar_Syntax_Syntax.Sig_let uu____84891) ->
                     let uu____84904 =
                       let uu____84907 =
                         let uu___4152_84908 = se2  in
                         let uu____84909 =
                           let uu____84912 =
                             FStar_List.filter
                               (fun uu___459_84926  ->
                                  match uu___459_84926 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____84931;
                                           FStar_Syntax_Syntax.vars =
                                             uu____84932;_},uu____84933);
                                      FStar_Syntax_Syntax.pos = uu____84934;
                                      FStar_Syntax_Syntax.vars = uu____84935;_}
                                      when
                                      let uu____84962 =
                                        let uu____84964 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____84964
                                         in
                                      uu____84962 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____84968 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84912
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84908.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84908.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84908.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84908.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84909
                         }  in
                       uu____84907 :: se1 :: acc  in
                     forward uu____84904 sigelts1
                 | uu____84974 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____84982 = forward [] sigelts  in (env1, uu____84982)
  
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
          | (FStar_Pervasives_Native.None ,uu____85047) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85051;
               FStar_Syntax_Syntax.exports = uu____85052;
               FStar_Syntax_Syntax.is_interface = uu____85053;_},FStar_Parser_AST.Module
             (current_lid,uu____85055)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85064) ->
              let uu____85067 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85067
           in
        let uu____85072 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85114 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85114, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85136 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85136, mname, decls, false)
           in
        match uu____85072 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85178 = desugar_decls env2 decls  in
            (match uu____85178 with
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
          let uu____85246 =
            (FStar_Options.interactive ()) &&
              (let uu____85249 =
                 let uu____85251 =
                   let uu____85253 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85253  in
                 FStar_Util.get_file_extension uu____85251  in
               FStar_List.mem uu____85249 ["fsti"; "fsi"])
             in
          if uu____85246 then as_interface m else m  in
        let uu____85267 = desugar_modul_common curmod env m1  in
        match uu____85267 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85289 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85289, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85311 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85311 with
      | (env1,modul,pop_when_done) ->
          let uu____85328 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85328 with
           | (env2,modul1) ->
               ((let uu____85340 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85340
                 then
                   let uu____85343 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85343
                 else ());
                (let uu____85348 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85348, modul1))))
  
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
        (fun uu____85402  ->
           let uu____85403 = desugar_modul env modul  in
           match uu____85403 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85445  ->
           let uu____85446 = desugar_decls env decls  in
           match uu____85446 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85501  ->
             let uu____85502 = desugar_partial_modul modul env a_modul  in
             match uu____85502 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85601 ->
                  let t =
                    let uu____85611 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85611  in
                  let uu____85624 =
                    let uu____85625 = FStar_Syntax_Subst.compress t  in
                    uu____85625.FStar_Syntax_Syntax.n  in
                  (match uu____85624 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85637,uu____85638)
                       -> bs1
                   | uu____85663 -> failwith "Impossible")
               in
            let uu____85673 =
              let uu____85680 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85680
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85673 with
            | (binders,uu____85682,binders_opening) ->
                let erase_term t =
                  let uu____85690 =
                    let uu____85691 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85691  in
                  FStar_Syntax_Subst.close binders uu____85690  in
                let erase_tscheme uu____85709 =
                  match uu____85709 with
                  | (us,t) ->
                      let t1 =
                        let uu____85729 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85729 t  in
                      let uu____85732 =
                        let uu____85733 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85733  in
                      ([], uu____85732)
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
                    | uu____85756 ->
                        let bs =
                          let uu____85766 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85766  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85806 =
                          let uu____85807 =
                            let uu____85810 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85810  in
                          uu____85807.FStar_Syntax_Syntax.n  in
                        (match uu____85806 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85812,uu____85813) -> bs1
                         | uu____85838 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85846 =
                      let uu____85847 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85847  in
                    FStar_Syntax_Subst.close binders uu____85846  in
                  let uu___4311_85848 = action  in
                  let uu____85849 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85850 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85848.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85848.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85849;
                    FStar_Syntax_Syntax.action_typ = uu____85850
                  }  in
                let uu___4313_85851 = ed  in
                let uu____85852 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85853 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85854 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85855 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85856 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85857 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85858 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85859 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85860 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85861 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85862 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85863 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85864 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85865 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85866 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85867 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85851.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85851.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85852;
                  FStar_Syntax_Syntax.signature = uu____85853;
                  FStar_Syntax_Syntax.ret_wp = uu____85854;
                  FStar_Syntax_Syntax.bind_wp = uu____85855;
                  FStar_Syntax_Syntax.if_then_else = uu____85856;
                  FStar_Syntax_Syntax.ite_wp = uu____85857;
                  FStar_Syntax_Syntax.stronger = uu____85858;
                  FStar_Syntax_Syntax.close_wp = uu____85859;
                  FStar_Syntax_Syntax.assert_p = uu____85860;
                  FStar_Syntax_Syntax.assume_p = uu____85861;
                  FStar_Syntax_Syntax.null_wp = uu____85862;
                  FStar_Syntax_Syntax.trivial = uu____85863;
                  FStar_Syntax_Syntax.repr = uu____85864;
                  FStar_Syntax_Syntax.return_repr = uu____85865;
                  FStar_Syntax_Syntax.bind_repr = uu____85866;
                  FStar_Syntax_Syntax.actions = uu____85867;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85851.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85883 = se  in
                  let uu____85884 =
                    let uu____85885 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85885  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85884;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85883.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85883.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85883.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85883.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85889 = se  in
                  let uu____85890 =
                    let uu____85891 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85891
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85890;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85889.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85889.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85889.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85889.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85893 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85894 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85894 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85911 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85911
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85913 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85913)
  