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
             (fun uu____57570  ->
                match uu____57570 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57625  ->
                             match uu____57625 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57643 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57643 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57649 =
                                     let uu____57650 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57650]  in
                                   FStar_Syntax_Subst.close uu____57649
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
      fun uu___429_57707  ->
        match uu___429_57707 with
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
  fun uu___430_57727  ->
    match uu___430_57727 with
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
  fun uu___431_57745  ->
    match uu___431_57745 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57748 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57756 .
    FStar_Parser_AST.imp ->
      'Auu____57756 ->
        ('Auu____57756 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57782 .
    FStar_Parser_AST.imp ->
      'Auu____57782 ->
        ('Auu____57782 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57801 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57822 -> true
            | uu____57828 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57837 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57844 =
      let uu____57845 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57845  in
    FStar_Parser_AST.mk_term uu____57844 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57855 =
      let uu____57856 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57856  in
    FStar_Parser_AST.mk_term uu____57855 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57872 =
        let uu____57873 = unparen t  in uu____57873.FStar_Parser_AST.tm  in
      match uu____57872 with
      | FStar_Parser_AST.Name l ->
          let uu____57876 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57876 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57883) ->
          let uu____57896 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57896 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57903,uu____57904) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57909,uu____57910) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57915,t1) -> is_comp_type env t1
      | uu____57917 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____58018;
                            FStar_Syntax_Syntax.vars = uu____58019;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58047 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58047 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____58063 =
                               let uu____58064 =
                                 let uu____58067 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____58067  in
                               uu____58064.FStar_Syntax_Syntax.n  in
                             match uu____58063 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58090))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58097 -> msg
                           else msg  in
                         let uu____58100 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58100
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58105 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58105 " is deprecated"  in
                         let uu____58108 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58108
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58110 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58126 .
    'Auu____58126 ->
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
        let uu____58179 =
          let uu____58182 =
            let uu____58183 =
              let uu____58189 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58189, r)  in
            FStar_Ident.mk_ident uu____58183  in
          [uu____58182]  in
        FStar_All.pipe_right uu____58179 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58205 .
    env_t ->
      Prims.int ->
        'Auu____58205 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58243 =
              let uu____58244 =
                let uu____58245 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58245 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58244 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58243  in
          let fallback uu____58253 =
            let uu____58254 = FStar_Ident.text_of_id op  in
            match uu____58254 with
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
                let uu____58275 = FStar_Options.ml_ish ()  in
                if uu____58275
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
            | uu____58300 -> FStar_Pervasives_Native.None  in
          let uu____58302 =
            let uu____58305 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58311 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58311.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58311.FStar_Syntax_Syntax.vars)
                 }) env true uu____58305
             in
          match uu____58302 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58316 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58331 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58331
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58380 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58384 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58384 with | (env1,uu____58396) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58399,term) ->
          let uu____58401 = free_type_vars env term  in (env, uu____58401)
      | FStar_Parser_AST.TAnnotated (id1,uu____58407) ->
          let uu____58408 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58408 with | (env1,uu____58420) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58424 = free_type_vars env t  in (env, uu____58424)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58431 =
        let uu____58432 = unparen t  in uu____58432.FStar_Parser_AST.tm  in
      match uu____58431 with
      | FStar_Parser_AST.Labeled uu____58435 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58448 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58448 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58453 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58456 -> []
      | FStar_Parser_AST.Uvar uu____58457 -> []
      | FStar_Parser_AST.Var uu____58458 -> []
      | FStar_Parser_AST.Projector uu____58459 -> []
      | FStar_Parser_AST.Discrim uu____58464 -> []
      | FStar_Parser_AST.Name uu____58465 -> []
      | FStar_Parser_AST.Requires (t1,uu____58467) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58475) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58482,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58501,ts) ->
          FStar_List.collect
            (fun uu____58522  ->
               match uu____58522 with
               | (t1,uu____58530) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58531,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58539) ->
          let uu____58540 = free_type_vars env t1  in
          let uu____58543 = free_type_vars env t2  in
          FStar_List.append uu____58540 uu____58543
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58548 = free_type_vars_b env b  in
          (match uu____58548 with
           | (env1,f) ->
               let uu____58563 = free_type_vars env1 t1  in
               FStar_List.append f uu____58563)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58580 =
            FStar_List.fold_left
              (fun uu____58604  ->
                 fun bt  ->
                   match uu____58604 with
                   | (env1,free) ->
                       let uu____58628 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58643 = free_type_vars env1 body  in
                             (env1, uu____58643)
                          in
                       (match uu____58628 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58580 with
           | (env1,free) ->
               let uu____58672 = free_type_vars env1 body  in
               FStar_List.append free uu____58672)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58681 =
            FStar_List.fold_left
              (fun uu____58701  ->
                 fun binder  ->
                   match uu____58701 with
                   | (env1,free) ->
                       let uu____58721 = free_type_vars_b env1 binder  in
                       (match uu____58721 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58681 with
           | (env1,free) ->
               let uu____58752 = free_type_vars env1 body  in
               FStar_List.append free uu____58752)
      | FStar_Parser_AST.Project (t1,uu____58756) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58767 = free_type_vars env rel  in
          let uu____58770 =
            let uu____58773 = free_type_vars env init1  in
            let uu____58776 =
              FStar_List.collect
                (fun uu____58785  ->
                   match uu____58785 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58791 = free_type_vars env rel1  in
                       let uu____58794 =
                         let uu____58797 = free_type_vars env just  in
                         let uu____58800 = free_type_vars env next  in
                         FStar_List.append uu____58797 uu____58800  in
                       FStar_List.append uu____58791 uu____58794) steps
               in
            FStar_List.append uu____58773 uu____58776  in
          FStar_List.append uu____58767 uu____58770
      | FStar_Parser_AST.Abs uu____58803 -> []
      | FStar_Parser_AST.Let uu____58810 -> []
      | FStar_Parser_AST.LetOpen uu____58831 -> []
      | FStar_Parser_AST.If uu____58836 -> []
      | FStar_Parser_AST.QForall uu____58843 -> []
      | FStar_Parser_AST.QExists uu____58856 -> []
      | FStar_Parser_AST.Record uu____58869 -> []
      | FStar_Parser_AST.Match uu____58882 -> []
      | FStar_Parser_AST.TryWith uu____58897 -> []
      | FStar_Parser_AST.Bind uu____58912 -> []
      | FStar_Parser_AST.Quote uu____58919 -> []
      | FStar_Parser_AST.VQuote uu____58924 -> []
      | FStar_Parser_AST.Antiquote uu____58925 -> []
      | FStar_Parser_AST.Seq uu____58926 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58980 =
        let uu____58981 = unparen t1  in uu____58981.FStar_Parser_AST.tm  in
      match uu____58980 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____59023 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____59048 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59048  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59070 =
                     let uu____59071 =
                       let uu____59076 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59076)  in
                     FStar_Parser_AST.TAnnotated uu____59071  in
                   FStar_Parser_AST.mk_binder uu____59070
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
        let uu____59094 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59094  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59116 =
                     let uu____59117 =
                       let uu____59122 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59122)  in
                     FStar_Parser_AST.TAnnotated uu____59117  in
                   FStar_Parser_AST.mk_binder uu____59116
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59124 =
             let uu____59125 = unparen t  in uu____59125.FStar_Parser_AST.tm
              in
           match uu____59124 with
           | FStar_Parser_AST.Product uu____59126 -> t
           | uu____59133 ->
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
      | uu____59170 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59181 -> true
    | FStar_Parser_AST.PatTvar (uu____59185,uu____59186) -> true
    | FStar_Parser_AST.PatVar (uu____59192,uu____59193) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59200) -> is_var_pattern p1
    | uu____59213 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59224) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59237;
           FStar_Parser_AST.prange = uu____59238;_},uu____59239)
        -> true
    | uu____59251 -> false
  
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
    | uu____59267 -> p
  
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
            let uu____59340 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59340 with
             | (name,args,uu____59383) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59433);
               FStar_Parser_AST.prange = uu____59434;_},args)
            when is_top_level1 ->
            let uu____59444 =
              let uu____59449 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59449  in
            (uu____59444, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59471);
               FStar_Parser_AST.prange = uu____59472;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59502 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59561 -> acc
        | FStar_Parser_AST.PatName uu____59564 -> acc
        | FStar_Parser_AST.PatOp uu____59565 -> acc
        | FStar_Parser_AST.PatConst uu____59566 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59583) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59589) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59598) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59615 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59615
        | FStar_Parser_AST.PatAscribed (pat,uu____59623) ->
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
    match projectee with | LocalBinder _0 -> true | uu____59705 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59747 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59796  ->
    match uu___432_59796 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59803 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59836  ->
    match uu____59836 with
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
      let uu____59918 =
        let uu____59935 =
          let uu____59938 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59938  in
        let uu____59939 =
          let uu____59950 =
            let uu____59959 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59959)  in
          [uu____59950]  in
        (uu____59935, uu____59939)  in
      FStar_Syntax_Syntax.Tm_app uu____59918  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____60008 =
        let uu____60025 =
          let uu____60028 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____60028  in
        let uu____60029 =
          let uu____60040 =
            let uu____60049 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____60049)  in
          [uu____60040]  in
        (uu____60025, uu____60029)  in
      FStar_Syntax_Syntax.Tm_app uu____60008  in
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
          let uu____60112 =
            let uu____60129 =
              let uu____60132 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60132  in
            let uu____60133 =
              let uu____60144 =
                let uu____60153 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60153)  in
              let uu____60161 =
                let uu____60172 =
                  let uu____60181 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60181)  in
                [uu____60172]  in
              uu____60144 :: uu____60161  in
            (uu____60129, uu____60133)  in
          FStar_Syntax_Syntax.Tm_app uu____60112  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60241 =
        let uu____60256 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60275  ->
               match uu____60275 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60286;
                    FStar_Syntax_Syntax.index = uu____60287;
                    FStar_Syntax_Syntax.sort = t;_},uu____60289)
                   ->
                   let uu____60297 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60297) uu____60256
         in
      FStar_All.pipe_right bs uu____60241  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60313 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60331 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60359 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60380,uu____60381,bs,t,uu____60384,uu____60385)
                            ->
                            let uu____60394 = bs_univnames bs  in
                            let uu____60397 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60394 uu____60397
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60400,uu____60401,t,uu____60403,uu____60404,uu____60405)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60412 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60359 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60421 = s  in
        let uu____60422 =
          let uu____60423 =
            let uu____60432 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60450,bs,t,lids1,lids2) ->
                          let uu___1027_60463 = se  in
                          let uu____60464 =
                            let uu____60465 =
                              let uu____60482 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60483 =
                                let uu____60484 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60484 t  in
                              (lid, uvs, uu____60482, uu____60483, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60465
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60464;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60463.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60463.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60463.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60463.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60498,t,tlid,n1,lids1) ->
                          let uu___1037_60509 = se  in
                          let uu____60510 =
                            let uu____60511 =
                              let uu____60527 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60527, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60511  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60510;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60509.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60509.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60509.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60509.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60531 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60432, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60423  in
        {
          FStar_Syntax_Syntax.sigel = uu____60422;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60421.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60421.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60421.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60421.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60538,t) ->
        let uvs =
          let uu____60541 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60541 FStar_Util.set_elements  in
        let uu___1046_60546 = s  in
        let uu____60547 =
          let uu____60548 =
            let uu____60555 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60555)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60548  in
        {
          FStar_Syntax_Syntax.sigel = uu____60547;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60546.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60546.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60546.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60546.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60579 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60582 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60589) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60622,(FStar_Util.Inl t,uu____60624),uu____60625)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60672,(FStar_Util.Inr c,uu____60674),uu____60675)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60722 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60723,(FStar_Util.Inl t,uu____60725),uu____60726) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60773,(FStar_Util.Inr c,uu____60775),uu____60776) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60823 -> empty_set  in
          FStar_Util.set_union uu____60579 uu____60582  in
        let all_lb_univs =
          let uu____60827 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60843 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60843) empty_set)
             in
          FStar_All.pipe_right uu____60827 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60853 = s  in
        let uu____60854 =
          let uu____60855 =
            let uu____60862 =
              let uu____60863 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60875 = lb  in
                        let uu____60876 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60879 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60875.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60876;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60875.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60879;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60875.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60875.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60863)  in
            (uu____60862, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60855  in
        {
          FStar_Syntax_Syntax.sigel = uu____60854;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60853.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60853.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60853.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60853.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60888,fml) ->
        let uvs =
          let uu____60891 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60891 FStar_Util.set_elements  in
        let uu___1112_60896 = s  in
        let uu____60897 =
          let uu____60898 =
            let uu____60905 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60905)  in
          FStar_Syntax_Syntax.Sig_assume uu____60898  in
        {
          FStar_Syntax_Syntax.sigel = uu____60897;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60896.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60896.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60896.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60896.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60907,bs,c,flags) ->
        let uvs =
          let uu____60916 =
            let uu____60919 = bs_univnames bs  in
            let uu____60922 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60919 uu____60922  in
          FStar_All.pipe_right uu____60916 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60930 = s  in
        let uu____60931 =
          let uu____60932 =
            let uu____60945 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60946 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60945, uu____60946, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60932  in
        {
          FStar_Syntax_Syntax.sigel = uu____60931;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60930.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60930.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60930.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60930.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60949 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60957  ->
    match uu___433_60957 with
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
    | uu____61008 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____61029 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____61029)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____61055 =
      let uu____61056 = unparen t  in uu____61056.FStar_Parser_AST.tm  in
    match uu____61055 with
    | FStar_Parser_AST.Wild  ->
        let uu____61062 =
          let uu____61063 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____61063  in
        FStar_Util.Inr uu____61062
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61076)) ->
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
             let uu____61167 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61167
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61184 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61184
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61200 =
               let uu____61206 =
                 let uu____61208 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61208
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61206)
                in
             FStar_Errors.raise_error uu____61200 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61217 ->
        let rec aux t1 univargs =
          let uu____61254 =
            let uu____61255 = unparen t1  in uu____61255.FStar_Parser_AST.tm
             in
          match uu____61254 with
          | FStar_Parser_AST.App (t2,targ,uu____61263) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61290  ->
                     match uu___434_61290 with
                     | FStar_Util.Inr uu____61297 -> true
                     | uu____61300 -> false) univargs
              then
                let uu____61308 =
                  let uu____61309 =
                    FStar_List.map
                      (fun uu___435_61319  ->
                         match uu___435_61319 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61309  in
                FStar_Util.Inr uu____61308
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61345  ->
                        match uu___436_61345 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61355 -> failwith "impossible")
                     univargs
                    in
                 let uu____61359 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61359)
          | uu____61375 ->
              let uu____61376 =
                let uu____61382 =
                  let uu____61384 =
                    let uu____61386 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61386 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61384  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61382)
                 in
              FStar_Errors.raise_error uu____61376 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61401 ->
        let uu____61402 =
          let uu____61408 =
            let uu____61410 =
              let uu____61412 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61412 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61410  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61408)  in
        FStar_Errors.raise_error uu____61402 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61453;_});
            FStar_Syntax_Syntax.pos = uu____61454;
            FStar_Syntax_Syntax.vars = uu____61455;_})::uu____61456
        ->
        let uu____61487 =
          let uu____61493 =
            let uu____61495 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61495
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61493)  in
        FStar_Errors.raise_error uu____61487 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61501 ->
        let uu____61520 =
          let uu____61526 =
            let uu____61528 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61528
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61526)  in
        FStar_Errors.raise_error uu____61520 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61541 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61541) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61569 = FStar_List.hd fields  in
        match uu____61569 with
        | (f,uu____61579) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61591 =
                match uu____61591 with
                | (f',uu____61597) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61599 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61599
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
              (let uu____61609 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61609);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61972 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61979 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61980 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61982,pats1) ->
              let aux out uu____62023 =
                match uu____62023 with
                | (p2,uu____62036) ->
                    let intersection =
                      let uu____62046 = pat_vars p2  in
                      FStar_Util.set_intersect uu____62046 out  in
                    let uu____62049 = FStar_Util.set_is_empty intersection
                       in
                    if uu____62049
                    then
                      let uu____62054 = pat_vars p2  in
                      FStar_Util.set_union out uu____62054
                    else
                      (let duplicate_bv =
                         let uu____62060 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____62060  in
                       let uu____62063 =
                         let uu____62069 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____62069)
                          in
                       FStar_Errors.raise_error uu____62063 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62093 = pat_vars p1  in
            FStar_All.pipe_right uu____62093 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62121 =
                let uu____62123 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62123  in
              if uu____62121
              then ()
              else
                (let nonlinear_vars =
                   let uu____62132 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62132  in
                 let first_nonlinear_var =
                   let uu____62136 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62136  in
                 let uu____62139 =
                   let uu____62145 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62145)  in
                 FStar_Errors.raise_error uu____62139 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62173 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62173 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62190 ->
            let uu____62193 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62193 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62344 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62368 =
              let uu____62369 =
                let uu____62370 =
                  let uu____62377 =
                    let uu____62378 =
                      let uu____62384 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62384, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62378  in
                  (uu____62377, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62370  in
              {
                FStar_Parser_AST.pat = uu____62369;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62368
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62404 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62407 = aux loc env1 p2  in
              match uu____62407 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62496 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62501 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62501.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62501.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62496.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62503 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62508 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62508.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62508.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62503.FStar_Syntax_Syntax.p)
                        }
                    | uu____62509 when top -> p4
                    | uu____62510 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62515 =
                    match binder with
                    | LetBinder uu____62536 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62561 = close_fun env1 t  in
                          desugar_term env1 uu____62561  in
                        let x1 =
                          let uu___1380_62563 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62563.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62563.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62515 with
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
            let uu____62631 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62631, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62645 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62645, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62669 = resolvex loc env1 x  in
            (match uu____62669 with
             | (loc1,env2,xbv) ->
                 let uu____62698 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62698, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62721 = resolvex loc env1 x  in
            (match uu____62721 with
             | (loc1,env2,xbv) ->
                 let uu____62750 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62750, [], imp))
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
            let uu____62765 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62765, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62795;_},args)
            ->
            let uu____62801 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62862  ->
                     match uu____62862 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62943 = aux loc1 env2 arg  in
                         (match uu____62943 with
                          | (loc2,env3,uu____62990,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62801 with
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
                 let uu____63122 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63122, annots, false))
        | FStar_Parser_AST.PatApp uu____63140 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63171 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63222  ->
                     match uu____63222 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63283 = aux loc1 env2 pat  in
                         (match uu____63283 with
                          | (loc2,env3,uu____63325,pat1,ans,uu____63328) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63171 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63425 =
                     let uu____63428 =
                       let uu____63435 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63435  in
                     let uu____63436 =
                       let uu____63437 =
                         let uu____63451 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63451, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63437  in
                     FStar_All.pipe_left uu____63428 uu____63436  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63485 =
                            let uu____63486 =
                              let uu____63500 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63500, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63486  in
                          FStar_All.pipe_left (pos_r r) uu____63485) pats1
                     uu____63425
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
            let uu____63558 =
              FStar_List.fold_left
                (fun uu____63618  ->
                   fun p2  ->
                     match uu____63618 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63700 = aux loc1 env2 p2  in
                         (match uu____63700 with
                          | (loc2,env3,uu____63747,pat,ans,uu____63750) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63558 with
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
                   | uu____63916 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63919 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63919, annots, false))
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
                   (fun uu____64000  ->
                      match uu____64000 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____64030  ->
                      match uu____64030 with
                      | (f,uu____64036) ->
                          let uu____64037 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____64063  ->
                                    match uu____64063 with
                                    | (g,uu____64070) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____64037 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64076,p2) ->
                               p2)))
               in
            let app =
              let uu____64083 =
                let uu____64084 =
                  let uu____64091 =
                    let uu____64092 =
                      let uu____64093 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64093  in
                    FStar_Parser_AST.mk_pattern uu____64092
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64091, args)  in
                FStar_Parser_AST.PatApp uu____64084  in
              FStar_Parser_AST.mk_pattern uu____64083
                p1.FStar_Parser_AST.prange
               in
            let uu____64096 = aux loc env1 app  in
            (match uu____64096 with
             | (env2,e,b,p2,annots,uu____64142) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64182 =
                         let uu____64183 =
                           let uu____64197 =
                             let uu___1528_64198 = fv  in
                             let uu____64199 =
                               let uu____64202 =
                                 let uu____64203 =
                                   let uu____64210 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64210)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64203
                                  in
                               FStar_Pervasives_Native.Some uu____64202  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64198.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64198.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64199
                             }  in
                           (uu____64197, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64183  in
                       FStar_All.pipe_left pos uu____64182
                   | uu____64236 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64322 = aux' true loc env1 p2  in
            (match uu____64322 with
             | (loc1,env2,var,p3,ans,uu____64366) ->
                 let uu____64381 =
                   FStar_List.fold_left
                     (fun uu____64430  ->
                        fun p4  ->
                          match uu____64430 with
                          | (loc2,env3,ps1) ->
                              let uu____64495 = aux' true loc2 env3 p4  in
                              (match uu____64495 with
                               | (loc3,env4,uu____64536,p5,ans1,uu____64539)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64381 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64700 ->
            let uu____64701 = aux' true loc env1 p1  in
            (match uu____64701 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64798 = aux_maybe_or env p  in
      match uu____64798 with
      | (env1,b,pats) ->
          ((let uu____64853 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64853
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
          let uu____64926 =
            let uu____64927 =
              let uu____64938 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64938, (ty, tacopt))  in
            LetBinder uu____64927  in
          (env, uu____64926, [])  in
        let op_to_ident x =
          let uu____64955 =
            let uu____64961 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64961, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64955  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64983 = op_to_ident x  in
              mklet uu____64983 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64985) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____64991;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65007 = op_to_ident x  in
              let uu____65008 = desugar_term env t  in
              mklet uu____65007 uu____65008 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____65010);
                 FStar_Parser_AST.prange = uu____65011;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65031 = desugar_term env t  in
              mklet x uu____65031 tacopt1
          | uu____65032 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____65045 = desugar_data_pat env p  in
           match uu____65045 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65074;
                      FStar_Syntax_Syntax.p = uu____65075;_},uu____65076)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65089;
                      FStar_Syntax_Syntax.p = uu____65090;_},uu____65091)::[]
                     -> []
                 | uu____65104 -> p1  in
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
  fun uu____65112  ->
    fun env  ->
      fun pat  ->
        let uu____65116 = desugar_data_pat env pat  in
        match uu____65116 with | (env1,uu____65132,pat1) -> (env1, pat1)

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
      let uu____65154 = desugar_term_aq env e  in
      match uu____65154 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65173 = desugar_typ_aq env e  in
      match uu____65173 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65183  ->
        fun range  ->
          match uu____65183 with
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
              ((let uu____65205 =
                  let uu____65207 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65207  in
                if uu____65205
                then
                  let uu____65210 =
                    let uu____65216 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65216)  in
                  FStar_Errors.log_issue range uu____65210
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
                  let uu____65237 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65237 range  in
                let lid1 =
                  let uu____65241 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65241 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65251 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65251 range  in
                           let private_fv =
                             let uu____65253 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65253 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65254 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65254.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65254.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65255 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65259 =
                        let uu____65265 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65265)
                         in
                      FStar_Errors.raise_error uu____65259 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65285 =
                  let uu____65292 =
                    let uu____65293 =
                      let uu____65310 =
                        let uu____65321 =
                          let uu____65330 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65330)  in
                        [uu____65321]  in
                      (lid1, uu____65310)  in
                    FStar_Syntax_Syntax.Tm_app uu____65293  in
                  FStar_Syntax_Syntax.mk uu____65292  in
                uu____65285 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65381 =
          let uu____65382 = unparen t  in uu____65382.FStar_Parser_AST.tm  in
        match uu____65381 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65383; FStar_Ident.ident = uu____65384;
              FStar_Ident.nsstr = uu____65385; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65390 ->
            let uu____65391 =
              let uu____65397 =
                let uu____65399 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65399  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65397)  in
            FStar_Errors.raise_error uu____65391 t.FStar_Parser_AST.range
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
          let uu___1725_65486 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65486.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65486.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65489 =
          let uu____65490 = unparen top  in uu____65490.FStar_Parser_AST.tm
           in
        match uu____65489 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65495 ->
            let uu____65504 = desugar_formula env top  in
            (uu____65504, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65513 = desugar_formula env t  in (uu____65513, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65522 = desugar_formula env t  in (uu____65522, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65549 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65549, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65551 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65551, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65560 =
                let uu____65561 =
                  let uu____65568 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65568, args)  in
                FStar_Parser_AST.Op uu____65561  in
              FStar_Parser_AST.mk_term uu____65560 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65573 =
              let uu____65574 =
                let uu____65575 =
                  let uu____65582 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65582, [e])  in
                FStar_Parser_AST.Op uu____65575  in
              FStar_Parser_AST.mk_term uu____65574 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65573
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65594 = FStar_Ident.text_of_id op_star  in
             uu____65594 = "*") &&
              (let uu____65599 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65599 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65616;_},t1::t2::[])
                  when
                  let uu____65622 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65622 FStar_Option.isNone ->
                  let uu____65629 = flatten1 t1  in
                  FStar_List.append uu____65629 [t2]
              | uu____65632 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65637 = top  in
              let uu____65638 =
                let uu____65639 =
                  let uu____65650 =
                    FStar_List.map (fun _65661  -> FStar_Util.Inr _65661)
                      terms
                     in
                  (uu____65650, rhs)  in
                FStar_Parser_AST.Sum uu____65639  in
              {
                FStar_Parser_AST.tm = uu____65638;
                FStar_Parser_AST.range =
                  (uu___1773_65637.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65637.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65669 =
              let uu____65670 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65670  in
            (uu____65669, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65676 =
              let uu____65682 =
                let uu____65684 =
                  let uu____65686 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65686 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65684  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65682)
               in
            FStar_Errors.raise_error uu____65676 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65701 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65701 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65708 =
                   let uu____65714 =
                     let uu____65716 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65716
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65714)
                    in
                 FStar_Errors.raise_error uu____65708
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65731 =
                     let uu____65756 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65818 = desugar_term_aq env t  in
                               match uu____65818 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65756 FStar_List.unzip  in
                   (match uu____65731 with
                    | (args1,aqs) ->
                        let uu____65951 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65951, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65968)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65985 =
              let uu___1802_65986 = top  in
              let uu____65987 =
                let uu____65988 =
                  let uu____65995 =
                    let uu___1804_65996 = top  in
                    let uu____65997 =
                      let uu____65998 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____65998  in
                    {
                      FStar_Parser_AST.tm = uu____65997;
                      FStar_Parser_AST.range =
                        (uu___1804_65996.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_65996.FStar_Parser_AST.level)
                    }  in
                  (uu____65995, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65988  in
              {
                FStar_Parser_AST.tm = uu____65987;
                FStar_Parser_AST.range =
                  (uu___1802_65986.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65986.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65985
        | FStar_Parser_AST.Construct (n1,(a,uu____66006)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____66026 =
                let uu___1814_66027 = top  in
                let uu____66028 =
                  let uu____66029 =
                    let uu____66036 =
                      let uu___1816_66037 = top  in
                      let uu____66038 =
                        let uu____66039 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____66039  in
                      {
                        FStar_Parser_AST.tm = uu____66038;
                        FStar_Parser_AST.range =
                          (uu___1816_66037.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_66037.FStar_Parser_AST.level)
                      }  in
                    (uu____66036, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____66029  in
                {
                  FStar_Parser_AST.tm = uu____66028;
                  FStar_Parser_AST.range =
                    (uu___1814_66027.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_66027.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____66026))
        | FStar_Parser_AST.Construct (n1,(a,uu____66047)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____66064 =
              let uu___1825_66065 = top  in
              let uu____66066 =
                let uu____66067 =
                  let uu____66074 =
                    let uu___1827_66075 = top  in
                    let uu____66076 =
                      let uu____66077 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66077  in
                    {
                      FStar_Parser_AST.tm = uu____66076;
                      FStar_Parser_AST.range =
                        (uu___1827_66075.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66075.FStar_Parser_AST.level)
                    }  in
                  (uu____66074, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____66067  in
              {
                FStar_Parser_AST.tm = uu____66066;
                FStar_Parser_AST.range =
                  (uu___1825_66065.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_66065.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____66064
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66083; FStar_Ident.ident = uu____66084;
              FStar_Ident.nsstr = uu____66085; FStar_Ident.str = "Type0";_}
            ->
            let uu____66090 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66090, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66091; FStar_Ident.ident = uu____66092;
              FStar_Ident.nsstr = uu____66093; FStar_Ident.str = "Type";_}
            ->
            let uu____66098 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66098, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66099; FStar_Ident.ident = uu____66100;
               FStar_Ident.nsstr = uu____66101; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66121 =
              let uu____66122 =
                let uu____66123 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66123  in
              mk1 uu____66122  in
            (uu____66121, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66124; FStar_Ident.ident = uu____66125;
              FStar_Ident.nsstr = uu____66126; FStar_Ident.str = "Effect";_}
            ->
            let uu____66131 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66131, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66132; FStar_Ident.ident = uu____66133;
              FStar_Ident.nsstr = uu____66134; FStar_Ident.str = "True";_}
            ->
            let uu____66139 =
              let uu____66140 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66140
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66139, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66141; FStar_Ident.ident = uu____66142;
              FStar_Ident.nsstr = uu____66143; FStar_Ident.str = "False";_}
            ->
            let uu____66148 =
              let uu____66149 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66149
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66148, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66152;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66155 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66155 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66164 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66164, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66166 =
                    let uu____66168 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66168 txt
                     in
                  failwith uu____66166))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66177 = desugar_name mk1 setpos env true l  in
              (uu____66177, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66186 = desugar_name mk1 setpos env true l  in
              (uu____66186, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66204 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66204 with
                | FStar_Pervasives_Native.Some uu____66214 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66222 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66222 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66240 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66261 =
                    let uu____66262 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66262  in
                  (uu____66261, noaqs)
              | uu____66268 ->
                  let uu____66276 =
                    let uu____66282 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66282)  in
                  FStar_Errors.raise_error uu____66276
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66292 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66292 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66299 =
                    let uu____66305 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66305)
                     in
                  FStar_Errors.raise_error uu____66299
                    top.FStar_Parser_AST.range
              | uu____66313 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66317 = desugar_name mk1 setpos env true lid'  in
                  (uu____66317, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66339 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66339 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66358 ->
                       let uu____66365 =
                         FStar_Util.take
                           (fun uu____66389  ->
                              match uu____66389 with
                              | (uu____66395,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66365 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66440 =
                              let uu____66465 =
                                FStar_List.map
                                  (fun uu____66508  ->
                                     match uu____66508 with
                                     | (t,imp) ->
                                         let uu____66525 =
                                           desugar_term_aq env t  in
                                         (match uu____66525 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66465
                                FStar_List.unzip
                               in
                            (match uu____66440 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66668 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66668, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66687 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66687 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66698 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66726  ->
                 match uu___437_66726 with
                 | FStar_Util.Inr uu____66732 -> true
                 | uu____66734 -> false) binders
            ->
            let terms =
              let uu____66743 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66760  ->
                        match uu___438_66760 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66766 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66743 [t]  in
            let uu____66768 =
              let uu____66793 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66850 = desugar_typ_aq env t1  in
                        match uu____66850 with
                        | (t',aq) ->
                            let uu____66861 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66861, aq)))
                 in
              FStar_All.pipe_right uu____66793 FStar_List.unzip  in
            (match uu____66768 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66971 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66971
                    in
                 let uu____66980 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66980, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____67007 =
              let uu____67024 =
                let uu____67031 =
                  let uu____67038 =
                    FStar_All.pipe_left
                      (fun _67047  -> FStar_Util.Inl _67047)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____67038]  in
                FStar_List.append binders uu____67031  in
              FStar_List.fold_left
                (fun uu____67092  ->
                   fun b  ->
                     match uu____67092 with
                     | (env1,tparams,typs) ->
                         let uu____67153 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67168 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67168)
                            in
                         (match uu____67153 with
                          | (xopt,t1) ->
                              let uu____67193 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67202 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67202)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67193 with
                               | (env2,x) ->
                                   let uu____67222 =
                                     let uu____67225 =
                                       let uu____67228 =
                                         let uu____67229 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67229
                                          in
                                       [uu____67228]  in
                                     FStar_List.append typs uu____67225  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67255 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67255.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67255.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67222)))) (env, [], [])
                uu____67024
               in
            (match uu____67007 with
             | (env1,uu____67283,targs) ->
                 let tup =
                   let uu____67306 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67306
                    in
                 let uu____67307 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67307, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67326 = uncurry binders t  in
            (match uu____67326 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67370 =
                   match uu___439_67370 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67387 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67387
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67411 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67411 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67444 = aux env [] bs  in (uu____67444, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67453 = desugar_binder env b  in
            (match uu____67453 with
             | (FStar_Pervasives_Native.None ,uu____67464) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67479 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67479 with
                  | ((x,uu____67495),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67508 =
                        let uu____67509 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67509  in
                      (uu____67508, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67588 = FStar_Util.set_is_empty i  in
                    if uu____67588
                    then
                      let uu____67593 = FStar_Util.set_union acc set1  in
                      aux uu____67593 sets2
                    else
                      (let uu____67598 =
                         let uu____67599 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67599  in
                       FStar_Pervasives_Native.Some uu____67598)
                 in
              let uu____67602 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67602 sets  in
            ((let uu____67606 = check_disjoint bvss  in
              match uu____67606 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67610 =
                    let uu____67616 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67616)
                     in
                  let uu____67620 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67610 uu____67620);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67628 =
                FStar_List.fold_left
                  (fun uu____67648  ->
                     fun pat  ->
                       match uu____67648 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67674,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67684 =
                                  let uu____67687 = free_type_vars env1 t  in
                                  FStar_List.append uu____67687 ftvs  in
                                (env1, uu____67684)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67692,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67703 =
                                  let uu____67706 = free_type_vars env1 t  in
                                  let uu____67709 =
                                    let uu____67712 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67712 ftvs  in
                                  FStar_List.append uu____67706 uu____67709
                                   in
                                (env1, uu____67703)
                            | uu____67717 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67628 with
              | (uu____67726,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67738 =
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
                    FStar_List.append uu____67738 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67795 =
                    match uu___440_67795 with
                    | [] ->
                        let uu____67822 = desugar_term_aq env1 body  in
                        (match uu____67822 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67859 =
                                       let uu____67860 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67860
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67859
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
                             let uu____67929 =
                               let uu____67932 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67932  in
                             (uu____67929, aq))
                    | p::rest ->
                        let uu____67947 = desugar_binding_pat env1 p  in
                        (match uu____67947 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67981)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____67996 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____68005 =
                               match b with
                               | LetBinder uu____68046 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68115) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68169 =
                                           let uu____68178 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68178, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68169
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68240,uu____68241) ->
                                              let tup2 =
                                                let uu____68243 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68243
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68248 =
                                                  let uu____68255 =
                                                    let uu____68256 =
                                                      let uu____68273 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68276 =
                                                        let uu____68287 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68296 =
                                                          let uu____68307 =
                                                            let uu____68316 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68316
                                                             in
                                                          [uu____68307]  in
                                                        uu____68287 ::
                                                          uu____68296
                                                         in
                                                      (uu____68273,
                                                        uu____68276)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68256
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68255
                                                   in
                                                uu____68248
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68367 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68367
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68418,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68420,pats)) ->
                                              let tupn =
                                                let uu____68465 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68465
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68478 =
                                                  let uu____68479 =
                                                    let uu____68496 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68499 =
                                                      let uu____68510 =
                                                        let uu____68521 =
                                                          let uu____68530 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68530
                                                           in
                                                        [uu____68521]  in
                                                      FStar_List.append args
                                                        uu____68510
                                                       in
                                                    (uu____68496,
                                                      uu____68499)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68479
                                                   in
                                                mk1 uu____68478  in
                                              let p2 =
                                                let uu____68578 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68578
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68625 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____68005 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68719,uu____68720,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68742 =
                let uu____68743 = unparen e  in
                uu____68743.FStar_Parser_AST.tm  in
              match uu____68742 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68753 ->
                  let uu____68754 = desugar_term_aq env e  in
                  (match uu____68754 with
                   | (head1,aq) ->
                       let uu____68767 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68767, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68774 ->
            let rec aux args aqs e =
              let uu____68851 =
                let uu____68852 = unparen e  in
                uu____68852.FStar_Parser_AST.tm  in
              match uu____68851 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68870 = desugar_term_aq env t  in
                  (match uu____68870 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68918 ->
                  let uu____68919 = desugar_term_aq env e  in
                  (match uu____68919 with
                   | (head1,aq) ->
                       let uu____68940 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68940, (join_aqs (aq :: aqs))))
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
            let uu____69003 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____69003
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
            let uu____69055 = desugar_term_aq env t  in
            (match uu____69055 with
             | (tm,s) ->
                 let uu____69066 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____69066, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____69072 =
              let uu____69085 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69085 then desugar_typ_aq else desugar_term_aq  in
            uu____69072 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69144 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69287  ->
                        match uu____69287 with
                        | (attr_opt,(p,def)) ->
                            let uu____69345 = is_app_pattern p  in
                            if uu____69345
                            then
                              let uu____69378 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69378, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69461 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69461, def1)
                               | uu____69506 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69544);
                                           FStar_Parser_AST.prange =
                                             uu____69545;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69594 =
                                            let uu____69615 =
                                              let uu____69620 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69620  in
                                            (uu____69615, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69594, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69712) ->
                                        if top_level
                                        then
                                          let uu____69748 =
                                            let uu____69769 =
                                              let uu____69774 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69774  in
                                            (uu____69769, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69748, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69865 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69898 =
                FStar_List.fold_left
                  (fun uu____69971  ->
                     fun uu____69972  ->
                       match (uu____69971, uu____69972) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70080,uu____70081),uu____70082))
                           ->
                           let uu____70199 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70225 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70225 with
                                  | (env2,xx) ->
                                      let uu____70244 =
                                        let uu____70247 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70247 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70244))
                             | FStar_Util.Inr l ->
                                 let uu____70255 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70255, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70199 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69898 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70403 =
                    match uu____70403 with
                    | (attrs_opt,(uu____70439,args,result_t),def) ->
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
                                let uu____70527 = is_comp_type env1 t  in
                                if uu____70527
                                then
                                  ((let uu____70531 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70541 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70541))
                                       in
                                    match uu____70531 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70548 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70551 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70551))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70548
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
                          | uu____70562 ->
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
                              let uu____70577 =
                                let uu____70578 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70578
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70577
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
                  let uu____70659 = desugar_term_aq env' body  in
                  (match uu____70659 with
                   | (body1,aq) ->
                       let uu____70672 =
                         let uu____70675 =
                           let uu____70676 =
                             let uu____70690 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70690)  in
                           FStar_Syntax_Syntax.Tm_let uu____70676  in
                         FStar_All.pipe_left mk1 uu____70675  in
                       (uu____70672, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70765 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70765 with
              | (env1,binder,pat1) ->
                  let uu____70787 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70813 = desugar_term_aq env1 t2  in
                        (match uu____70813 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70827 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70827
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70828 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70828, aq))
                    | LocalBinder (x,uu____70861) ->
                        let uu____70862 = desugar_term_aq env1 t2  in
                        (match uu____70862 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70876;
                                    FStar_Syntax_Syntax.p = uu____70877;_},uu____70878)::[]
                                   -> body1
                               | uu____70891 ->
                                   let uu____70894 =
                                     let uu____70901 =
                                       let uu____70902 =
                                         let uu____70925 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70928 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70925, uu____70928)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70902
                                        in
                                     FStar_Syntax_Syntax.mk uu____70901  in
                                   uu____70894 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70968 =
                               let uu____70971 =
                                 let uu____70972 =
                                   let uu____70986 =
                                     let uu____70989 =
                                       let uu____70990 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70990]  in
                                     FStar_Syntax_Subst.close uu____70989
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70986)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70972  in
                               FStar_All.pipe_left mk1 uu____70971  in
                             (uu____70968, aq))
                     in
                  (match uu____70787 with | (tm,aq) -> (tm, aq))
               in
            let uu____71052 = FStar_List.hd lbs  in
            (match uu____71052 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71096 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71096
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71112 =
                let uu____71113 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71113  in
              mk1 uu____71112  in
            let uu____71114 = desugar_term_aq env t1  in
            (match uu____71114 with
             | (t1',aq1) ->
                 let uu____71125 = desugar_term_aq env t2  in
                 (match uu____71125 with
                  | (t2',aq2) ->
                      let uu____71136 = desugar_term_aq env t3  in
                      (match uu____71136 with
                       | (t3',aq3) ->
                           let uu____71147 =
                             let uu____71148 =
                               let uu____71149 =
                                 let uu____71172 =
                                   let uu____71189 =
                                     let uu____71204 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71204,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71218 =
                                     let uu____71235 =
                                       let uu____71250 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71250,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71235]  in
                                   uu____71189 :: uu____71218  in
                                 (t1', uu____71172)  in
                               FStar_Syntax_Syntax.Tm_match uu____71149  in
                             mk1 uu____71148  in
                           (uu____71147, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71446 =
              match uu____71446 with
              | (pat,wopt,b) ->
                  let uu____71468 = desugar_match_pat env pat  in
                  (match uu____71468 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71499 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71499
                          in
                       let uu____71504 = desugar_term_aq env1 b  in
                       (match uu____71504 with
                        | (b1,aq) ->
                            let uu____71517 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71517, aq)))
               in
            let uu____71522 = desugar_term_aq env e  in
            (match uu____71522 with
             | (e1,aq) ->
                 let uu____71533 =
                   let uu____71564 =
                     let uu____71597 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71597 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71564
                     (fun uu____71815  ->
                        match uu____71815 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71533 with
                  | (brs,aqs) ->
                      let uu____72034 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____72034, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____72068 =
              let uu____72089 = is_comp_type env t  in
              if uu____72089
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72144 = desugar_term_aq env t  in
                 match uu____72144 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____72068 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72236 = desugar_term_aq env e  in
                 (match uu____72236 with
                  | (e1,aq) ->
                      let uu____72247 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72247, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72286,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72329 = FStar_List.hd fields  in
              match uu____72329 with | (f,uu____72341) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72387  ->
                        match uu____72387 with
                        | (g,uu____72394) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72401,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72415 =
                         let uu____72421 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72421)
                          in
                       FStar_Errors.raise_error uu____72415
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
                  let uu____72432 =
                    let uu____72443 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72474  ->
                              match uu____72474 with
                              | (f,uu____72484) ->
                                  let uu____72485 =
                                    let uu____72486 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72486
                                     in
                                  (uu____72485, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72443)  in
                  FStar_Parser_AST.Construct uu____72432
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72504 =
                      let uu____72505 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72505  in
                    FStar_Parser_AST.mk_term uu____72504
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72507 =
                      let uu____72520 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72550  ->
                                match uu____72550 with
                                | (f,uu____72560) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72520)  in
                    FStar_Parser_AST.Record uu____72507  in
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
            let uu____72620 = desugar_term_aq env recterm1  in
            (match uu____72620 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72636;
                         FStar_Syntax_Syntax.vars = uu____72637;_},args)
                      ->
                      let uu____72663 =
                        let uu____72664 =
                          let uu____72665 =
                            let uu____72682 =
                              let uu____72685 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72686 =
                                let uu____72689 =
                                  let uu____72690 =
                                    let uu____72697 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72697)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72690
                                   in
                                FStar_Pervasives_Native.Some uu____72689  in
                              FStar_Syntax_Syntax.fvar uu____72685
                                FStar_Syntax_Syntax.delta_constant
                                uu____72686
                               in
                            (uu____72682, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72665  in
                        FStar_All.pipe_left mk1 uu____72664  in
                      (uu____72663, s)
                  | uu____72726 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72730 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72730 with
              | (constrname,is_rec) ->
                  let uu____72749 = desugar_term_aq env e  in
                  (match uu____72749 with
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
                       let uu____72769 =
                         let uu____72770 =
                           let uu____72771 =
                             let uu____72788 =
                               let uu____72791 =
                                 let uu____72792 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72792
                                  in
                               FStar_Syntax_Syntax.fvar uu____72791
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72794 =
                               let uu____72805 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72805]  in
                             (uu____72788, uu____72794)  in
                           FStar_Syntax_Syntax.Tm_app uu____72771  in
                         FStar_All.pipe_left mk1 uu____72770  in
                       (uu____72769, s))))
        | FStar_Parser_AST.NamedTyp (uu____72842,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72852 =
              let uu____72853 = FStar_Syntax_Subst.compress tm  in
              uu____72853.FStar_Syntax_Syntax.n  in
            (match uu____72852 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72861 =
                   let uu___2520_72862 =
                     let uu____72863 =
                       let uu____72865 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72865  in
                     FStar_Syntax_Util.exp_string uu____72863  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72862.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72862.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72861, noaqs)
             | uu____72866 ->
                 let uu____72867 =
                   let uu____72873 =
                     let uu____72875 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72875
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72873)  in
                 FStar_Errors.raise_error uu____72867
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72884 = desugar_term_aq env e  in
            (match uu____72884 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72896 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72896, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72901 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72902 =
              let uu____72903 =
                let uu____72910 = desugar_term env e  in (bv, uu____72910)
                 in
              [uu____72903]  in
            (uu____72901, uu____72902)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72935 =
              let uu____72936 =
                let uu____72937 =
                  let uu____72944 = desugar_term env e  in (uu____72944, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72937  in
              FStar_All.pipe_left mk1 uu____72936  in
            (uu____72935, noaqs)
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
              let uu____72973 =
                let uu____72974 =
                  let uu____72981 =
                    let uu____72982 =
                      let uu____72983 =
                        let uu____72992 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____73005 =
                          let uu____73006 =
                            let uu____73007 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____73007  in
                          FStar_Parser_AST.mk_term uu____73006
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____72992, uu____73005,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72983  in
                    FStar_Parser_AST.mk_term uu____72982
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72981)  in
                FStar_Parser_AST.Abs uu____72974  in
              FStar_Parser_AST.mk_term uu____72973
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
                   fun uu____73053  ->
                     match uu____73053 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____73057 =
                           let uu____73064 =
                             let uu____73069 = eta_and_annot rel2  in
                             (uu____73069, FStar_Parser_AST.Nothing)  in
                           let uu____73070 =
                             let uu____73077 =
                               let uu____73084 =
                                 let uu____73089 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73089, FStar_Parser_AST.Nothing)  in
                               let uu____73090 =
                                 let uu____73097 =
                                   let uu____73102 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73102, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73097]  in
                               uu____73084 :: uu____73090  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73077
                              in
                           uu____73064 :: uu____73070  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____73057
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73124 =
                let uu____73131 =
                  let uu____73136 = FStar_Parser_AST.thunk e1  in
                  (uu____73136, FStar_Parser_AST.Nothing)  in
                [uu____73131]  in
              FStar_Parser_AST.mkApp finish1 uu____73124
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73145 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73146 = desugar_formula env top  in
            (uu____73146, noaqs)
        | uu____73147 ->
            let uu____73148 =
              let uu____73154 =
                let uu____73156 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73156  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73154)  in
            FStar_Errors.raise_error uu____73148 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73166 -> false
    | uu____73176 -> true

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
           (fun uu____73214  ->
              match uu____73214 with
              | (a,imp) ->
                  let uu____73227 = desugar_term env a  in
                  arg_withimp_e imp uu____73227))

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
          let is_requires uu____73264 =
            match uu____73264 with
            | (t1,uu____73271) ->
                let uu____73272 =
                  let uu____73273 = unparen t1  in
                  uu____73273.FStar_Parser_AST.tm  in
                (match uu____73272 with
                 | FStar_Parser_AST.Requires uu____73275 -> true
                 | uu____73284 -> false)
             in
          let is_ensures uu____73296 =
            match uu____73296 with
            | (t1,uu____73303) ->
                let uu____73304 =
                  let uu____73305 = unparen t1  in
                  uu____73305.FStar_Parser_AST.tm  in
                (match uu____73304 with
                 | FStar_Parser_AST.Ensures uu____73307 -> true
                 | uu____73316 -> false)
             in
          let is_app head1 uu____73334 =
            match uu____73334 with
            | (t1,uu____73342) ->
                let uu____73343 =
                  let uu____73344 = unparen t1  in
                  uu____73344.FStar_Parser_AST.tm  in
                (match uu____73343 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73347;
                        FStar_Parser_AST.level = uu____73348;_},uu____73349,uu____73350)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73352 -> false)
             in
          let is_smt_pat uu____73364 =
            match uu____73364 with
            | (t1,uu____73371) ->
                let uu____73372 =
                  let uu____73373 = unparen t1  in
                  uu____73373.FStar_Parser_AST.tm  in
                (match uu____73372 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73377);
                               FStar_Parser_AST.range = uu____73378;
                               FStar_Parser_AST.level = uu____73379;_},uu____73380)::uu____73381::[])
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
                               FStar_Parser_AST.range = uu____73430;
                               FStar_Parser_AST.level = uu____73431;_},uu____73432)::uu____73433::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73466 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73501 = head_and_args t1  in
            match uu____73501 with
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
                     let thunk_ens uu____73594 =
                       match uu____73594 with
                       | (e,i) ->
                           let uu____73605 = FStar_Parser_AST.thunk e  in
                           (uu____73605, i)
                        in
                     let fail_lemma uu____73617 =
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
                           let uu____73723 =
                             let uu____73730 =
                               let uu____73737 = thunk_ens ens  in
                               [uu____73737; nil_pat]  in
                             req_true :: uu____73730  in
                           unit_tm :: uu____73723
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73784 =
                             let uu____73791 =
                               let uu____73798 = thunk_ens ens  in
                               [uu____73798; nil_pat]  in
                             req :: uu____73791  in
                           unit_tm :: uu____73784
                       | ens::smtpat::[] when
                           (((let uu____73847 = is_requires ens  in
                              Prims.op_Negation uu____73847) &&
                               (let uu____73850 = is_smt_pat ens  in
                                Prims.op_Negation uu____73850))
                              &&
                              (let uu____73853 = is_decreases ens  in
                               Prims.op_Negation uu____73853))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73855 =
                             let uu____73862 =
                               let uu____73869 = thunk_ens ens  in
                               [uu____73869; smtpat]  in
                             req_true :: uu____73862  in
                           unit_tm :: uu____73855
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73916 =
                             let uu____73923 =
                               let uu____73930 = thunk_ens ens  in
                               [uu____73930; nil_pat; dec]  in
                             req_true :: uu____73923  in
                           unit_tm :: uu____73916
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73990 =
                             let uu____73997 =
                               let uu____74004 = thunk_ens ens  in
                               [uu____74004; smtpat; dec]  in
                             req_true :: uu____73997  in
                           unit_tm :: uu____73990
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____74064 =
                             let uu____74071 =
                               let uu____74078 = thunk_ens ens  in
                               [uu____74078; nil_pat; dec]  in
                             req :: uu____74071  in
                           unit_tm :: uu____74064
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74138 =
                             let uu____74145 =
                               let uu____74152 = thunk_ens ens  in
                               [uu____74152; smtpat]  in
                             req :: uu____74145  in
                           unit_tm :: uu____74138
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74217 =
                             let uu____74224 =
                               let uu____74231 = thunk_ens ens  in
                               [uu____74231; dec; smtpat]  in
                             req :: uu____74224  in
                           unit_tm :: uu____74217
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74293 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74293, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74321 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74321
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74324 =
                       let uu____74331 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74331, [])  in
                     (uu____74324, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74349 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74349
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74352 =
                       let uu____74359 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74359, [])  in
                     (uu____74352, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74381 =
                       let uu____74388 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74388, [])  in
                     (uu____74381, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74411 when allow_type_promotion ->
                     let default_effect =
                       let uu____74413 = FStar_Options.ml_ish ()  in
                       if uu____74413
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74419 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74419
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74426 =
                       let uu____74433 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74433, [])  in
                     (uu____74426, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74456 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74475 = pre_process_comp_typ t  in
          match uu____74475 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74527 =
                    let uu____74533 =
                      let uu____74535 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74535
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74533)
                     in
                  fail1 uu____74527)
               else ();
               (let is_universe uu____74551 =
                  match uu____74551 with
                  | (uu____74557,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74559 = FStar_Util.take is_universe args  in
                match uu____74559 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74618  ->
                           match uu____74618 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74625 =
                      let uu____74640 = FStar_List.hd args1  in
                      let uu____74649 = FStar_List.tl args1  in
                      (uu____74640, uu____74649)  in
                    (match uu____74625 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74704 =
                           let is_decrease uu____74743 =
                             match uu____74743 with
                             | (t1,uu____74754) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74765;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74766;_},uu____74767::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74806 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74704 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74923  ->
                                        match uu____74923 with
                                        | (t1,uu____74933) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74942,(arg,uu____74944)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74983 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____75004 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____75016 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____75016
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____75023 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____75023
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____75033 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75033
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____75040 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____75040
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____75047 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____75047
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____75054 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____75054
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75075 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75075
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
                                                    let uu____75166 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75166
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
                                              | uu____75187 -> pat  in
                                            let uu____75188 =
                                              let uu____75199 =
                                                let uu____75210 =
                                                  let uu____75219 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75219, aq)  in
                                                [uu____75210]  in
                                              ens :: uu____75199  in
                                            req :: uu____75188
                                        | uu____75260 -> rest2
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
        | uu____75292 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75314 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75314.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75314.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75356 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75356.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75356.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75356.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75419 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75419)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75432 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75432 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75442 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75442.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75442.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75468 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75482 =
                     let uu____75485 =
                       let uu____75486 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75486]  in
                     no_annot_abs uu____75485 body2  in
                   FStar_All.pipe_left setpos uu____75482  in
                 let uu____75507 =
                   let uu____75508 =
                     let uu____75525 =
                       let uu____75528 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75528
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75530 =
                       let uu____75541 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75541]  in
                     (uu____75525, uu____75530)  in
                   FStar_Syntax_Syntax.Tm_app uu____75508  in
                 FStar_All.pipe_left mk1 uu____75507)
        | uu____75580 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75661 = q (rest, pats, body)  in
              let uu____75668 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75661 uu____75668
                FStar_Parser_AST.Formula
               in
            let uu____75669 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75669 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75678 -> failwith "impossible"  in
      let uu____75682 =
        let uu____75683 = unparen f  in uu____75683.FStar_Parser_AST.tm  in
      match uu____75682 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75696,uu____75697) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75709,uu____75710) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75742 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75742
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75778 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75778
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75822 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75827 =
        FStar_List.fold_left
          (fun uu____75860  ->
             fun b  ->
               match uu____75860 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75904 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75904.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75904.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75904.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75919 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75919 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75937 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75937.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75937.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75938 =
                               let uu____75945 =
                                 let uu____75950 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75950)  in
                               uu____75945 :: out  in
                             (env2, uu____75938))
                    | uu____75961 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75827 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____76034 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76034)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____76039 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76039)
      | FStar_Parser_AST.TVariable x ->
          let uu____76043 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____76043)
      | FStar_Parser_AST.NoName t ->
          let uu____76047 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____76047)
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
      fun uu___441_76055  ->
        match uu___441_76055 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76077 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76077, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76094 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76094 with
             | (env1,a1) ->
                 let uu____76111 =
                   let uu____76118 = trans_aqual env1 imp  in
                   ((let uu___2962_76124 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76124.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76124.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76118)
                    in
                 (uu____76111, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76132  ->
      match uu___442_76132 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76136 =
            let uu____76137 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76137  in
          FStar_Pervasives_Native.Some uu____76136
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76153) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76155) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76158 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76176 = binder_ident b  in
         FStar_Common.list_of_option uu____76176) bs
  
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
               (fun uu___443_76213  ->
                  match uu___443_76213 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76218 -> false))
           in
        let quals2 q =
          let uu____76232 =
            (let uu____76236 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76236) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76232
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76253 = FStar_Ident.range_of_lid disc_name  in
                let uu____76254 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76253;
                  FStar_Syntax_Syntax.sigquals = uu____76254;
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
            let uu____76294 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76332  ->
                        match uu____76332 with
                        | (x,uu____76343) ->
                            let uu____76348 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76348 with
                             | (field_name,uu____76356) ->
                                 let only_decl =
                                   ((let uu____76361 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76361)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76363 =
                                        let uu____76365 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76365.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76363)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76383 =
                                       FStar_List.filter
                                         (fun uu___444_76387  ->
                                            match uu___444_76387 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76390 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76383
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76405  ->
                                             match uu___445_76405 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76410 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76413 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76413;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76420 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76420
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76431 =
                                        let uu____76436 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76436  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76431;
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
                                      let uu____76440 =
                                        let uu____76441 =
                                          let uu____76448 =
                                            let uu____76451 =
                                              let uu____76452 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76452
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76451]  in
                                          ((false, [lb]), uu____76448)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76441
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76440;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76294 FStar_List.flatten
  
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
            (lid,uu____76501,t,uu____76503,n1,uu____76505) when
            let uu____76512 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76512 ->
            let uu____76514 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76514 with
             | (formals,uu____76532) ->
                 (match formals with
                  | [] -> []
                  | uu____76561 ->
                      let filter_records uu___446_76577 =
                        match uu___446_76577 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76580,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76592 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76594 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76594 with
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
                      let uu____76606 = FStar_Util.first_N n1 formals  in
                      (match uu____76606 with
                       | (uu____76635,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76669 -> []
  
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
                    let uu____76748 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76748
                    then
                      let uu____76754 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76754
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76758 =
                      let uu____76763 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76763  in
                    let uu____76764 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76770 =
                          let uu____76773 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76773  in
                        FStar_Syntax_Util.arrow typars uu____76770
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76778 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76758;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76764;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76778;
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
          let tycon_id uu___447_76832 =
            match uu___447_76832 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76834,uu____76835) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76845,uu____76846,uu____76847) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76857,uu____76858,uu____76859) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76889,uu____76890,uu____76891) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76937) ->
                let uu____76938 =
                  let uu____76939 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76939  in
                FStar_Parser_AST.mk_term uu____76938 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76941 =
                  let uu____76942 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76942  in
                FStar_Parser_AST.mk_term uu____76941 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76944) ->
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
              | uu____76975 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76983 =
                     let uu____76984 =
                       let uu____76991 = binder_to_term b  in
                       (out, uu____76991, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76984  in
                   FStar_Parser_AST.mk_term uu____76983
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_77003 =
            match uu___448_77003 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____77060  ->
                       match uu____77060 with
                       | (x,t,uu____77071) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77077 =
                    let uu____77078 =
                      let uu____77079 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77079  in
                    FStar_Parser_AST.mk_term uu____77078
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77077 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77086 = binder_idents parms  in id1 ::
                    uu____77086
                   in
                (FStar_List.iter
                   (fun uu____77104  ->
                      match uu____77104 with
                      | (f,uu____77114,uu____77115) ->
                          let uu____77120 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77120
                          then
                            let uu____77125 =
                              let uu____77131 =
                                let uu____77133 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77133
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77131)
                               in
                            FStar_Errors.raise_error uu____77125
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77139 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77166  ->
                            match uu____77166 with
                            | (x,uu____77176,uu____77177) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77139)))
            | uu____77235 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77275 =
            match uu___449_77275 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77299 = typars_of_binders _env binders  in
                (match uu____77299 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77335 =
                         let uu____77336 =
                           let uu____77337 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77337  in
                         FStar_Parser_AST.mk_term uu____77336
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77335 binders  in
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
            | uu____77348 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77391 =
              FStar_List.fold_left
                (fun uu____77425  ->
                   fun uu____77426  ->
                     match (uu____77425, uu____77426) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77495 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77495 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77391 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77586 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77586
                | uu____77587 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77595 = desugar_abstract_tc quals env [] tc  in
              (match uu____77595 with
               | (uu____77608,uu____77609,se,uu____77611) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77614,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77633 =
                                 let uu____77635 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77635  in
                               if uu____77633
                               then
                                 let uu____77638 =
                                   let uu____77644 =
                                     let uu____77646 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77646
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77644)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77638
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
                           | uu____77659 ->
                               let uu____77660 =
                                 let uu____77667 =
                                   let uu____77668 =
                                     let uu____77683 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77683)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77668
                                    in
                                 FStar_Syntax_Syntax.mk uu____77667  in
                               uu____77660 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77699 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77699.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77699.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77699.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77700 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77704 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77704
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77717 = typars_of_binders env binders  in
              (match uu____77717 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77751 =
                           FStar_Util.for_some
                             (fun uu___450_77754  ->
                                match uu___450_77754 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77757 -> false) quals
                            in
                         if uu____77751
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77765 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77765
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77770 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77776  ->
                               match uu___451_77776 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77779 -> false))
                        in
                     if uu____77770
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77793 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77793
                     then
                       let uu____77799 =
                         let uu____77806 =
                           let uu____77807 = unparen t  in
                           uu____77807.FStar_Parser_AST.tm  in
                         match uu____77806 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77828 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77858)::args_rev ->
                                   let uu____77870 =
                                     let uu____77871 = unparen last_arg  in
                                     uu____77871.FStar_Parser_AST.tm  in
                                   (match uu____77870 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77899 -> ([], args))
                               | uu____77908 -> ([], args)  in
                             (match uu____77828 with
                              | (cattributes,args1) ->
                                  let uu____77947 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77947))
                         | uu____77958 -> (t, [])  in
                       match uu____77799 with
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
                                  (fun uu___452_77981  ->
                                     match uu___452_77981 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77984 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____77993)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____78017 = tycon_record_as_variant trec  in
              (match uu____78017 with
               | (t,fs) ->
                   let uu____78034 =
                     let uu____78037 =
                       let uu____78038 =
                         let uu____78047 =
                           let uu____78050 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____78050  in
                         (uu____78047, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____78038  in
                     uu____78037 :: quals  in
                   desugar_tycon env d uu____78034 [t])
          | uu____78055::uu____78056 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78226 = et  in
                match uu____78226 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78456 ->
                         let trec = tc  in
                         let uu____78480 = tycon_record_as_variant trec  in
                         (match uu____78480 with
                          | (t,fs) ->
                              let uu____78540 =
                                let uu____78543 =
                                  let uu____78544 =
                                    let uu____78553 =
                                      let uu____78556 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78556  in
                                    (uu____78553, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78544
                                   in
                                uu____78543 :: quals1  in
                              collect_tcs uu____78540 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78646 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78646 with
                          | (env2,uu____78707,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78860 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78860 with
                          | (env2,uu____78921,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____79049 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79099 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79099 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79614  ->
                             match uu___454_79614 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79680,uu____79681);
                                    FStar_Syntax_Syntax.sigrng = uu____79682;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79683;
                                    FStar_Syntax_Syntax.sigmeta = uu____79684;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79685;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79749 =
                                     typars_of_binders env1 binders  in
                                   match uu____79749 with
                                   | (env2,tpars1) ->
                                       let uu____79776 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79776 with
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
                                 let uu____79805 =
                                   let uu____79824 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79824)
                                    in
                                 [uu____79805]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79884);
                                    FStar_Syntax_Syntax.sigrng = uu____79885;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79887;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79888;_},constrs,tconstr,quals1)
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
                                 let uu____79989 = push_tparams env1 tpars
                                    in
                                 (match uu____79989 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____80056  ->
                                             match uu____80056 with
                                             | (x,uu____80068) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____80073 =
                                        let uu____80100 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80210  ->
                                                  match uu____80210 with
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
                                                        let uu____80270 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80270
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
                                                                uu___453_80281
                                                                 ->
                                                                match uu___453_80281
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80293
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80301 =
                                                        let uu____80320 =
                                                          let uu____80321 =
                                                            let uu____80322 =
                                                              let uu____80338
                                                                =
                                                                let uu____80339
                                                                  =
                                                                  let uu____80342
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80342
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80339
                                                                 in
                                                              (name, univs1,
                                                                uu____80338,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80322
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80321;
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
                                                          uu____80320)
                                                         in
                                                      (name, uu____80301)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80100
                                         in
                                      (match uu____80073 with
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
                             | uu____80558 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80686  ->
                             match uu____80686 with
                             | (name_doc,uu____80712,uu____80713) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80785  ->
                             match uu____80785 with
                             | (uu____80804,uu____80805,se) -> se))
                      in
                   let uu____80831 =
                     let uu____80838 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80838 rng
                      in
                   (match uu____80831 with
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
                               (fun uu____80900  ->
                                  match uu____80900 with
                                  | (uu____80921,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80969,tps,k,uu____80972,constrs)
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
                                      let uu____80993 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____81008 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____81025,uu____81026,uu____81027,uu____81028,uu____81029)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____81036
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____81008
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____81040 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_81047 
                                                          ->
                                                          match uu___455_81047
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____81049 ->
                                                              true
                                                          | uu____81059 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____81040))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____80993
                                  | uu____81061 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81078  ->
                                 match uu____81078 with
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
      let uu____81123 =
        FStar_List.fold_left
          (fun uu____81158  ->
             fun b  ->
               match uu____81158 with
               | (env1,binders1) ->
                   let uu____81202 = desugar_binder env1 b  in
                   (match uu____81202 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81225 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81225 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81278 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81123 with
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
          let uu____81382 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81389  ->
                    match uu___456_81389 with
                    | FStar_Syntax_Syntax.Reflectable uu____81391 -> true
                    | uu____81393 -> false))
             in
          if uu____81382
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81398 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81398
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
      let uu____81439 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81439 with
      | (hd1,args) ->
          let uu____81492 =
            let uu____81507 =
              let uu____81508 = FStar_Syntax_Subst.compress hd1  in
              uu____81508.FStar_Syntax_Syntax.n  in
            (uu____81507, args)  in
          (match uu____81492 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81533)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81568 =
                 let uu____81573 =
                   let uu____81582 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81582 a1  in
                 uu____81573 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81568 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81612 =
                      let uu____81621 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81621, b)  in
                    FStar_Pervasives_Native.Some uu____81612
                | uu____81638 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81692) when
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
           | uu____81727 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81899 = desugar_binders monad_env eff_binders  in
                  match uu____81899 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81939 =
                          let uu____81941 =
                            let uu____81950 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81950  in
                          FStar_List.length uu____81941  in
                        uu____81939 = (Prims.parse_int "1")  in
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
                            (uu____82034,uu____82035,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____82037,uu____82038,uu____82039),uu____82040)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82077 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82080 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82092 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82092 mandatory_members)
                          eff_decls
                         in
                      (match uu____82080 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82111 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82140  ->
                                     fun decl  ->
                                       match uu____82140 with
                                       | (env2,out) ->
                                           let uu____82160 =
                                             desugar_decl env2 decl  in
                                           (match uu____82160 with
                                            | (env3,ses) ->
                                                let uu____82173 =
                                                  let uu____82176 =
                                                    FStar_List.hd ses  in
                                                  uu____82176 :: out  in
                                                (env3, uu____82173)))
                                  (env1, []))
                              in
                           (match uu____82111 with
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
                                              (uu____82245,uu____82246,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82249,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82250,(def,uu____82252)::
                                                      (cps_type,uu____82254)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82255;
                                                   FStar_Parser_AST.level =
                                                     uu____82256;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82312 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82312 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82350 =
                                                     let uu____82351 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82352 =
                                                       let uu____82353 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82353
                                                        in
                                                     let uu____82360 =
                                                       let uu____82361 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82361
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82351;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82352;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82360
                                                     }  in
                                                   (uu____82350, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82370,uu____82371,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82374,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82413 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82413 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82451 =
                                                     let uu____82452 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82453 =
                                                       let uu____82454 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82454
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82452;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82453;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82451, doc1))
                                          | uu____82463 ->
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
                                    let uu____82499 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82499
                                     in
                                  let uu____82501 =
                                    let uu____82502 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82502
                                     in
                                  ([], uu____82501)  in
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
                                      let uu____82520 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82520)  in
                                    let uu____82527 =
                                      let uu____82528 =
                                        let uu____82529 =
                                          let uu____82530 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82530
                                           in
                                        let uu____82540 = lookup1 "return"
                                           in
                                        let uu____82542 = lookup1 "bind"  in
                                        let uu____82544 =
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
                                            uu____82529;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82540;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82542;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82544
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82528
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82527;
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
                                         (fun uu___457_82552  ->
                                            match uu___457_82552 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82555 -> true
                                            | uu____82557 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82572 =
                                       let uu____82573 =
                                         let uu____82574 =
                                           lookup1 "return_wp"  in
                                         let uu____82576 = lookup1 "bind_wp"
                                            in
                                         let uu____82578 =
                                           lookup1 "if_then_else"  in
                                         let uu____82580 = lookup1 "ite_wp"
                                            in
                                         let uu____82582 = lookup1 "stronger"
                                            in
                                         let uu____82584 = lookup1 "close_wp"
                                            in
                                         let uu____82586 = lookup1 "assert_p"
                                            in
                                         let uu____82588 = lookup1 "assume_p"
                                            in
                                         let uu____82590 = lookup1 "null_wp"
                                            in
                                         let uu____82592 = lookup1 "trivial"
                                            in
                                         let uu____82594 =
                                           if rr
                                           then
                                             let uu____82596 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82596
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82614 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82619 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82624 =
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
                                             uu____82574;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82576;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82578;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82580;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82582;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82584;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82586;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82588;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82590;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82592;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82594;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82614;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82619;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82624
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82573
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82572;
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
                                          fun uu____82650  ->
                                            match uu____82650 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82664 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82664
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
                let uu____82688 = desugar_binders env1 eff_binders  in
                match uu____82688 with
                | (env2,binders) ->
                    let uu____82725 =
                      let uu____82736 = head_and_args defn  in
                      match uu____82736 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82773 ->
                                let uu____82774 =
                                  let uu____82780 =
                                    let uu____82782 =
                                      let uu____82784 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82784 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82782  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82780)
                                   in
                                FStar_Errors.raise_error uu____82774
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82790 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82820)::args_rev ->
                                let uu____82832 =
                                  let uu____82833 = unparen last_arg  in
                                  uu____82833.FStar_Parser_AST.tm  in
                                (match uu____82832 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82861 -> ([], args))
                            | uu____82870 -> ([], args)  in
                          (match uu____82790 with
                           | (cattributes,args1) ->
                               let uu____82913 = desugar_args env2 args1  in
                               let uu____82914 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82913, uu____82914))
                       in
                    (match uu____82725 with
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
                          (let uu____82954 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82954 with
                           | (ed_binders,uu____82968,ed_binders_opening) ->
                               let sub' shift_n uu____82987 =
                                 match uu____82987 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____83002 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____83002 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____83006 =
                                       let uu____83007 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____83007)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____83006
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____83028 =
                                   let uu____83029 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____83029
                                    in
                                 let uu____83044 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____83045 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____83046 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____83047 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____83048 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____83049 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____83050 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____83051 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____83052 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____83053 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____83054 =
                                   let uu____83055 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____83055
                                    in
                                 let uu____83070 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____83071 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____83072 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83088 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83089 =
                                          let uu____83090 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83090
                                           in
                                        let uu____83111 =
                                          let uu____83112 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83112
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83088;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83089;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83111
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
                                     uu____83028;
                                   FStar_Syntax_Syntax.ret_wp = uu____83044;
                                   FStar_Syntax_Syntax.bind_wp = uu____83045;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____83046;
                                   FStar_Syntax_Syntax.ite_wp = uu____83047;
                                   FStar_Syntax_Syntax.stronger = uu____83048;
                                   FStar_Syntax_Syntax.close_wp = uu____83049;
                                   FStar_Syntax_Syntax.assert_p = uu____83050;
                                   FStar_Syntax_Syntax.assume_p = uu____83051;
                                   FStar_Syntax_Syntax.null_wp = uu____83052;
                                   FStar_Syntax_Syntax.trivial = uu____83053;
                                   FStar_Syntax_Syntax.repr = uu____83054;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____83070;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____83071;
                                   FStar_Syntax_Syntax.actions = uu____83072;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83136 =
                                     let uu____83138 =
                                       let uu____83147 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83147
                                        in
                                     FStar_List.length uu____83138  in
                                   uu____83136 = (Prims.parse_int "1")  in
                                 let uu____83180 =
                                   let uu____83183 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83183 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____83180;
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
                                             let uu____83207 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83207
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83209 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83209
                                 then
                                   let reflect_lid =
                                     let uu____83216 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83216
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
    let uu____83228 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83228 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83313 ->
              let uu____83316 =
                let uu____83318 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83318
                 in
              Prims.op_Hat "\n  " uu____83316
          | uu____83321 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83340  ->
               match uu____83340 with
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
          let uu____83385 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83385
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83388 =
          let uu____83399 = FStar_Syntax_Syntax.as_arg arg  in [uu____83399]
           in
        FStar_Syntax_Util.mk_app fv uu____83388

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83430 = desugar_decl_noattrs env d  in
      match uu____83430 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83448 = mk_comment_attr d  in uu____83448 :: attrs1  in
          let uu____83449 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83459 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83459.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83459.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83459.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83459.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83462 = sigelt  in
                      let uu____83463 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83469 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83469) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83462.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83462.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83462.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83462.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83463
                      })) sigelts
             in
          (env1, uu____83449)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83495 = desugar_decl_aux env d  in
      match uu____83495 with
      | (env1,ses) ->
          let uu____83506 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83506)

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
      | FStar_Parser_AST.Fsdoc uu____83534 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83539 = FStar_Syntax_DsEnv.iface env  in
          if uu____83539
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83554 =
               let uu____83556 =
                 let uu____83558 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83559 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83558
                   uu____83559
                  in
               Prims.op_Negation uu____83556  in
             if uu____83554
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83573 =
                  let uu____83575 =
                    let uu____83577 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83577 lid  in
                  Prims.op_Negation uu____83575  in
                if uu____83573
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83591 =
                     let uu____83593 =
                       let uu____83595 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83595
                         lid
                        in
                     Prims.op_Negation uu____83593  in
                   if uu____83591
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83613 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83613, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83654,uu____83655)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83694 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83721  ->
                 match uu____83721 with | (x,uu____83729) -> x) tcs
             in
          let uu____83734 =
            let uu____83739 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83739 tcs1  in
          (match uu____83734 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83756 =
                   let uu____83757 =
                     let uu____83764 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83764  in
                   [uu____83757]  in
                 let uu____83777 =
                   let uu____83780 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83783 =
                     let uu____83794 =
                       let uu____83803 =
                         let uu____83804 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83804  in
                       FStar_Syntax_Syntax.as_arg uu____83803  in
                     [uu____83794]  in
                   FStar_Syntax_Util.mk_app uu____83780 uu____83783  in
                 FStar_Syntax_Util.abs uu____83756 uu____83777
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83844,id1))::uu____83846 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83849::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83853 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83853 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83859 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83859]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83880) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83890,uu____83891,uu____83892,uu____83893,uu____83894)
                     ->
                     let uu____83903 =
                       let uu____83904 =
                         let uu____83905 =
                           let uu____83912 = mkclass lid  in
                           (meths, uu____83912)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83905  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83904;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83903]
                 | uu____83915 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83949;
                    FStar_Parser_AST.prange = uu____83950;_},uu____83951)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83961;
                    FStar_Parser_AST.prange = uu____83962;_},uu____83963)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83979;
                         FStar_Parser_AST.prange = uu____83980;_},uu____83981);
                    FStar_Parser_AST.prange = uu____83982;_},uu____83983)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____84005;
                         FStar_Parser_AST.prange = uu____84006;_},uu____84007);
                    FStar_Parser_AST.prange = uu____84008;_},uu____84009)::[]
                   -> false
               | (p,uu____84038)::[] ->
                   let uu____84047 = is_app_pattern p  in
                   Prims.op_Negation uu____84047
               | uu____84049 -> false)
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
            let uu____84124 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84124 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84137 =
                     let uu____84138 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84138.FStar_Syntax_Syntax.n  in
                   match uu____84137 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84148) ->
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
                         | uu____84184::uu____84185 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84188 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84204  ->
                                     match uu___458_84204 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84207;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84208;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84209;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84210;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84211;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84212;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84213;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84225;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84226;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84227;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84228;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84229;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84230;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84244 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84277  ->
                                   match uu____84277 with
                                   | (uu____84291,(uu____84292,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84244
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84312 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84312
                         then
                           let uu____84318 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84333 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84335 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84335.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84335.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84333.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84318)
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
                   | uu____84365 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84373 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84392 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84373 with
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
                       let uu___4019_84429 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84429.FStar_Parser_AST.prange)
                       }
                   | uu____84436 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84443 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84443.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84443.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84443.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84479 id1 =
                   match uu____84479 with
                   | (env1,ses) ->
                       let main =
                         let uu____84500 =
                           let uu____84501 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84501  in
                         FStar_Parser_AST.mk_term uu____84500
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
                       let uu____84551 = desugar_decl env1 id_decl  in
                       (match uu____84551 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84569 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84569 FStar_Util.set_elements
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
            let uu____84593 = close_fun env t  in
            desugar_term env uu____84593  in
          let quals1 =
            let uu____84597 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84597
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84609 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84609;
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
                let uu____84623 =
                  let uu____84632 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84632]  in
                let uu____84651 =
                  let uu____84654 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84654
                   in
                FStar_Syntax_Util.arrow uu____84623 uu____84651
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
            let uu____84709 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84709 with
            | FStar_Pervasives_Native.None  ->
                let uu____84712 =
                  let uu____84718 =
                    let uu____84720 =
                      let uu____84722 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84722 " not found"  in
                    Prims.op_Hat "Effect name " uu____84720  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84718)  in
                FStar_Errors.raise_error uu____84712
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84730 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84748 =
                  let uu____84751 =
                    let uu____84752 = desugar_term env t  in
                    ([], uu____84752)  in
                  FStar_Pervasives_Native.Some uu____84751  in
                (uu____84748, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84765 =
                  let uu____84768 =
                    let uu____84769 = desugar_term env wp  in
                    ([], uu____84769)  in
                  FStar_Pervasives_Native.Some uu____84768  in
                let uu____84776 =
                  let uu____84779 =
                    let uu____84780 = desugar_term env t  in
                    ([], uu____84780)  in
                  FStar_Pervasives_Native.Some uu____84779  in
                (uu____84765, uu____84776)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84792 =
                  let uu____84795 =
                    let uu____84796 = desugar_term env t  in
                    ([], uu____84796)  in
                  FStar_Pervasives_Native.Some uu____84795  in
                (FStar_Pervasives_Native.None, uu____84792)
             in
          (match uu____84730 with
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
            let uu____84830 =
              let uu____84831 =
                let uu____84838 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84838, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84831  in
            {
              FStar_Syntax_Syntax.sigel = uu____84830;
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
      let uu____84865 =
        FStar_List.fold_left
          (fun uu____84885  ->
             fun d  ->
               match uu____84885 with
               | (env1,sigelts) ->
                   let uu____84905 = desugar_decl env1 d  in
                   (match uu____84905 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84865 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84950 =
            match uu___460_84950 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84964,FStar_Syntax_Syntax.Sig_let uu____84965) ->
                     let uu____84978 =
                       let uu____84981 =
                         let uu___4152_84982 = se2  in
                         let uu____84983 =
                           let uu____84986 =
                             FStar_List.filter
                               (fun uu___459_85000  ->
                                  match uu___459_85000 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____85005;
                                           FStar_Syntax_Syntax.vars =
                                             uu____85006;_},uu____85007);
                                      FStar_Syntax_Syntax.pos = uu____85008;
                                      FStar_Syntax_Syntax.vars = uu____85009;_}
                                      when
                                      let uu____85036 =
                                        let uu____85038 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____85038
                                         in
                                      uu____85036 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____85042 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84986
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84982.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84982.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84982.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84982.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84983
                         }  in
                       uu____84981 :: se1 :: acc  in
                     forward uu____84978 sigelts1
                 | uu____85048 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____85056 = forward [] sigelts  in (env1, uu____85056)
  
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
          | (FStar_Pervasives_Native.None ,uu____85121) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85125;
               FStar_Syntax_Syntax.exports = uu____85126;
               FStar_Syntax_Syntax.is_interface = uu____85127;_},FStar_Parser_AST.Module
             (current_lid,uu____85129)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85138) ->
              let uu____85141 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85141
           in
        let uu____85146 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85188 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85188, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85210 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85210, mname, decls, false)
           in
        match uu____85146 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85252 = desugar_decls env2 decls  in
            (match uu____85252 with
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
          let uu____85320 =
            (FStar_Options.interactive ()) &&
              (let uu____85323 =
                 let uu____85325 =
                   let uu____85327 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85327  in
                 FStar_Util.get_file_extension uu____85325  in
               FStar_List.mem uu____85323 ["fsti"; "fsi"])
             in
          if uu____85320 then as_interface m else m  in
        let uu____85341 = desugar_modul_common curmod env m1  in
        match uu____85341 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85363 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85363, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85385 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85385 with
      | (env1,modul,pop_when_done) ->
          let uu____85402 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85402 with
           | (env2,modul1) ->
               ((let uu____85414 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85414
                 then
                   let uu____85417 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85417
                 else ());
                (let uu____85422 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85422, modul1))))
  
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
        (fun uu____85476  ->
           let uu____85477 = desugar_modul env modul  in
           match uu____85477 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85519  ->
           let uu____85520 = desugar_decls env decls  in
           match uu____85520 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85575  ->
             let uu____85576 = desugar_partial_modul modul env a_modul  in
             match uu____85576 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85675 ->
                  let t =
                    let uu____85685 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85685  in
                  let uu____85698 =
                    let uu____85699 = FStar_Syntax_Subst.compress t  in
                    uu____85699.FStar_Syntax_Syntax.n  in
                  (match uu____85698 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85711,uu____85712)
                       -> bs1
                   | uu____85737 -> failwith "Impossible")
               in
            let uu____85747 =
              let uu____85754 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85754
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85747 with
            | (binders,uu____85756,binders_opening) ->
                let erase_term t =
                  let uu____85764 =
                    let uu____85765 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85765  in
                  FStar_Syntax_Subst.close binders uu____85764  in
                let erase_tscheme uu____85783 =
                  match uu____85783 with
                  | (us,t) ->
                      let t1 =
                        let uu____85803 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85803 t  in
                      let uu____85806 =
                        let uu____85807 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85807  in
                      ([], uu____85806)
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
                    | uu____85830 ->
                        let bs =
                          let uu____85840 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85840  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85880 =
                          let uu____85881 =
                            let uu____85884 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85884  in
                          uu____85881.FStar_Syntax_Syntax.n  in
                        (match uu____85880 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85886,uu____85887) -> bs1
                         | uu____85912 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85920 =
                      let uu____85921 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85921  in
                    FStar_Syntax_Subst.close binders uu____85920  in
                  let uu___4311_85922 = action  in
                  let uu____85923 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85924 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85922.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85922.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85923;
                    FStar_Syntax_Syntax.action_typ = uu____85924
                  }  in
                let uu___4313_85925 = ed  in
                let uu____85926 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85927 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85928 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85929 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85930 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85931 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85932 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85933 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85934 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85935 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85936 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85937 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85938 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85939 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85940 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85941 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85925.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85925.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85926;
                  FStar_Syntax_Syntax.signature = uu____85927;
                  FStar_Syntax_Syntax.ret_wp = uu____85928;
                  FStar_Syntax_Syntax.bind_wp = uu____85929;
                  FStar_Syntax_Syntax.if_then_else = uu____85930;
                  FStar_Syntax_Syntax.ite_wp = uu____85931;
                  FStar_Syntax_Syntax.stronger = uu____85932;
                  FStar_Syntax_Syntax.close_wp = uu____85933;
                  FStar_Syntax_Syntax.assert_p = uu____85934;
                  FStar_Syntax_Syntax.assume_p = uu____85935;
                  FStar_Syntax_Syntax.null_wp = uu____85936;
                  FStar_Syntax_Syntax.trivial = uu____85937;
                  FStar_Syntax_Syntax.repr = uu____85938;
                  FStar_Syntax_Syntax.return_repr = uu____85939;
                  FStar_Syntax_Syntax.bind_repr = uu____85940;
                  FStar_Syntax_Syntax.actions = uu____85941;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85925.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85957 = se  in
                  let uu____85958 =
                    let uu____85959 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85959  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85958;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85957.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85957.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85957.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85957.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85963 = se  in
                  let uu____85964 =
                    let uu____85965 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85965
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85964;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85963.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85963.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85963.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85963.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85967 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85968 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85968 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85985 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85985
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85987 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85987)
  