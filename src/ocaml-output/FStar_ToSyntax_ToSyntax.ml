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
             (fun uu____52772  ->
                match uu____52772 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____52827  ->
                             match uu____52827 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____52845 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____52845 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____52851 =
                                     let uu____52852 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____52852]  in
                                   FStar_Syntax_Subst.close uu____52851
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
      fun uu___429_52909  ->
        match uu___429_52909 with
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
  fun uu___430_52929  ->
    match uu___430_52929 with
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
  fun uu___431_52947  ->
    match uu___431_52947 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____52950 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____52958 .
    FStar_Parser_AST.imp ->
      'Auu____52958 ->
        ('Auu____52958 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____52984 .
    FStar_Parser_AST.imp ->
      'Auu____52984 ->
        ('Auu____52984 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53003 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53024 -> true
            | uu____53030 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53039 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53046 =
      let uu____53047 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53047  in
    FStar_Parser_AST.mk_term uu____53046 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53057 =
      let uu____53058 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53058  in
    FStar_Parser_AST.mk_term uu____53057 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53074 =
        let uu____53075 = unparen t  in uu____53075.FStar_Parser_AST.tm  in
      match uu____53074 with
      | FStar_Parser_AST.Name l ->
          let uu____53078 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53078 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53085) ->
          let uu____53098 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53098 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53105,uu____53106) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53111,uu____53112) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53117,t1) -> is_comp_type env t1
      | uu____53119 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53220;
                            FStar_Syntax_Syntax.vars = uu____53221;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53249 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53249 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53265 =
                               let uu____53266 =
                                 let uu____53269 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____53269  in
                               uu____53266.FStar_Syntax_Syntax.n  in
                             match uu____53265 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____53292))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____53299 -> msg
                           else msg  in
                         let uu____53302 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53302
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53307 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53307 " is deprecated"  in
                         let uu____53310 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53310
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____53312 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____53328 .
    'Auu____53328 ->
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
        let uu____53381 =
          let uu____53384 =
            let uu____53385 =
              let uu____53391 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____53391, r)  in
            FStar_Ident.mk_ident uu____53385  in
          [uu____53384]  in
        FStar_All.pipe_right uu____53381 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____53407 .
    env_t ->
      Prims.int ->
        'Auu____53407 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____53445 =
              let uu____53446 =
                let uu____53447 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____53447 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____53446 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____53445  in
          let fallback uu____53455 =
            let uu____53456 = FStar_Ident.text_of_id op  in
            match uu____53456 with
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
                let uu____53477 = FStar_Options.ml_ish ()  in
                if uu____53477
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
            | uu____53502 -> FStar_Pervasives_Native.None  in
          let uu____53504 =
            let uu____53507 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_53513 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_53513.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_53513.FStar_Syntax_Syntax.vars)
                 }) env true uu____53507
             in
          match uu____53504 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____53518 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____53533 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____53533
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____53582 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____53586 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____53586 with | (env1,uu____53598) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____53601,term) ->
          let uu____53603 = free_type_vars env term  in (env, uu____53603)
      | FStar_Parser_AST.TAnnotated (id1,uu____53609) ->
          let uu____53610 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____53610 with | (env1,uu____53622) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____53626 = free_type_vars env t  in (env, uu____53626)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____53633 =
        let uu____53634 = unparen t  in uu____53634.FStar_Parser_AST.tm  in
      match uu____53633 with
      | FStar_Parser_AST.Labeled uu____53637 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____53650 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____53650 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____53655 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____53658 -> []
      | FStar_Parser_AST.Uvar uu____53659 -> []
      | FStar_Parser_AST.Var uu____53660 -> []
      | FStar_Parser_AST.Projector uu____53661 -> []
      | FStar_Parser_AST.Discrim uu____53666 -> []
      | FStar_Parser_AST.Name uu____53667 -> []
      | FStar_Parser_AST.Requires (t1,uu____53669) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____53677) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____53684,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____53703,ts) ->
          FStar_List.collect
            (fun uu____53724  ->
               match uu____53724 with
               | (t1,uu____53732) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____53733,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____53741) ->
          let uu____53742 = free_type_vars env t1  in
          let uu____53745 = free_type_vars env t2  in
          FStar_List.append uu____53742 uu____53745
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____53750 = free_type_vars_b env b  in
          (match uu____53750 with
           | (env1,f) ->
               let uu____53765 = free_type_vars env1 t1  in
               FStar_List.append f uu____53765)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____53782 =
            FStar_List.fold_left
              (fun uu____53806  ->
                 fun bt  ->
                   match uu____53806 with
                   | (env1,free) ->
                       let uu____53830 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____53845 = free_type_vars env1 body  in
                             (env1, uu____53845)
                          in
                       (match uu____53830 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53782 with
           | (env1,free) ->
               let uu____53874 = free_type_vars env1 body  in
               FStar_List.append free uu____53874)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____53883 =
            FStar_List.fold_left
              (fun uu____53903  ->
                 fun binder  ->
                   match uu____53903 with
                   | (env1,free) ->
                       let uu____53923 = free_type_vars_b env1 binder  in
                       (match uu____53923 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53883 with
           | (env1,free) ->
               let uu____53954 = free_type_vars env1 body  in
               FStar_List.append free uu____53954)
      | FStar_Parser_AST.Project (t1,uu____53958) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____53969 = free_type_vars env rel  in
          let uu____53972 =
            let uu____53975 = free_type_vars env init1  in
            let uu____53978 =
              FStar_List.collect
                (fun uu____53987  ->
                   match uu____53987 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____53993 = free_type_vars env rel1  in
                       let uu____53996 =
                         let uu____53999 = free_type_vars env just  in
                         let uu____54002 = free_type_vars env next  in
                         FStar_List.append uu____53999 uu____54002  in
                       FStar_List.append uu____53993 uu____53996) steps
               in
            FStar_List.append uu____53975 uu____53978  in
          FStar_List.append uu____53969 uu____53972
      | FStar_Parser_AST.Abs uu____54005 -> []
      | FStar_Parser_AST.Let uu____54012 -> []
      | FStar_Parser_AST.LetOpen uu____54033 -> []
      | FStar_Parser_AST.If uu____54038 -> []
      | FStar_Parser_AST.QForall uu____54045 -> []
      | FStar_Parser_AST.QExists uu____54058 -> []
      | FStar_Parser_AST.Record uu____54071 -> []
      | FStar_Parser_AST.Match uu____54084 -> []
      | FStar_Parser_AST.TryWith uu____54099 -> []
      | FStar_Parser_AST.Bind uu____54114 -> []
      | FStar_Parser_AST.Quote uu____54121 -> []
      | FStar_Parser_AST.VQuote uu____54126 -> []
      | FStar_Parser_AST.Antiquote uu____54127 -> []
      | FStar_Parser_AST.Seq uu____54128 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54182 =
        let uu____54183 = unparen t1  in uu____54183.FStar_Parser_AST.tm  in
      match uu____54182 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54225 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54250 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54250  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54272 =
                     let uu____54273 =
                       let uu____54278 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54278)  in
                     FStar_Parser_AST.TAnnotated uu____54273  in
                   FStar_Parser_AST.mk_binder uu____54272
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
        let uu____54296 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54296  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54318 =
                     let uu____54319 =
                       let uu____54324 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54324)  in
                     FStar_Parser_AST.TAnnotated uu____54319  in
                   FStar_Parser_AST.mk_binder uu____54318
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____54326 =
             let uu____54327 = unparen t  in uu____54327.FStar_Parser_AST.tm
              in
           match uu____54326 with
           | FStar_Parser_AST.Product uu____54328 -> t
           | uu____54335 ->
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
      | uu____54372 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____54383 -> true
    | FStar_Parser_AST.PatTvar (uu____54387,uu____54388) -> true
    | FStar_Parser_AST.PatVar (uu____54394,uu____54395) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____54402) -> is_var_pattern p1
    | uu____54415 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____54426) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____54439;
           FStar_Parser_AST.prange = uu____54440;_},uu____54441)
        -> true
    | uu____54453 -> false
  
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
    | uu____54469 -> p
  
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
            let uu____54542 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____54542 with
             | (name,args,uu____54585) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54635);
               FStar_Parser_AST.prange = uu____54636;_},args)
            when is_top_level1 ->
            let uu____54646 =
              let uu____54651 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____54651  in
            (uu____54646, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54673);
               FStar_Parser_AST.prange = uu____54674;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____54704 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____54763 -> acc
        | FStar_Parser_AST.PatName uu____54766 -> acc
        | FStar_Parser_AST.PatOp uu____54767 -> acc
        | FStar_Parser_AST.PatConst uu____54768 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____54785) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____54791) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____54800) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____54817 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____54817
        | FStar_Parser_AST.PatAscribed (pat,uu____54825) ->
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
    match projectee with | LocalBinder _0 -> true | uu____54907 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____54948 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_54996  ->
    match uu___432_54996 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55003 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55036  ->
    match uu____55036 with
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
      let uu____55118 =
        let uu____55135 =
          let uu____55138 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55138  in
        let uu____55139 =
          let uu____55150 =
            let uu____55159 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55159)  in
          [uu____55150]  in
        (uu____55135, uu____55139)  in
      FStar_Syntax_Syntax.Tm_app uu____55118  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55208 =
        let uu____55225 =
          let uu____55228 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55228  in
        let uu____55229 =
          let uu____55240 =
            let uu____55249 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55249)  in
          [uu____55240]  in
        (uu____55225, uu____55229)  in
      FStar_Syntax_Syntax.Tm_app uu____55208  in
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
          let uu____55312 =
            let uu____55329 =
              let uu____55332 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____55332  in
            let uu____55333 =
              let uu____55344 =
                let uu____55353 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____55353)  in
              let uu____55361 =
                let uu____55372 =
                  let uu____55381 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____55381)  in
                [uu____55372]  in
              uu____55344 :: uu____55361  in
            (uu____55329, uu____55333)  in
          FStar_Syntax_Syntax.Tm_app uu____55312  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____55441 =
        let uu____55456 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____55475  ->
               match uu____55475 with
               | ({ FStar_Syntax_Syntax.ppname = uu____55486;
                    FStar_Syntax_Syntax.index = uu____55487;
                    FStar_Syntax_Syntax.sort = t;_},uu____55489)
                   ->
                   let uu____55497 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____55497) uu____55456
         in
      FStar_All.pipe_right bs uu____55441  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____55513 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____55531 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____55559 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____55580,uu____55581,bs,t,uu____55584,uu____55585)
                            ->
                            let uu____55594 = bs_univnames bs  in
                            let uu____55597 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____55594 uu____55597
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____55600,uu____55601,t,uu____55603,uu____55604,uu____55605)
                            -> FStar_Syntax_Free.univnames t
                        | uu____55612 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____55559 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_55621 = s  in
        let uu____55622 =
          let uu____55623 =
            let uu____55632 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____55650,bs,t,lids1,lids2) ->
                          let uu___1027_55663 = se  in
                          let uu____55664 =
                            let uu____55665 =
                              let uu____55682 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____55683 =
                                let uu____55684 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____55684 t  in
                              (lid, uvs, uu____55682, uu____55683, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____55665
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55664;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_55663.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_55663.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_55663.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_55663.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____55698,t,tlid,n1,lids1) ->
                          let uu___1037_55709 = se  in
                          let uu____55710 =
                            let uu____55711 =
                              let uu____55727 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____55727, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____55711  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55710;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_55709.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_55709.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_55709.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_55709.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____55731 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____55632, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____55623  in
        {
          FStar_Syntax_Syntax.sigel = uu____55622;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_55621.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_55621.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_55621.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_55621.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____55738,t) ->
        let uvs =
          let uu____55741 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____55741 FStar_Util.set_elements  in
        let uu___1046_55746 = s  in
        let uu____55747 =
          let uu____55748 =
            let uu____55755 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____55755)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____55748  in
        {
          FStar_Syntax_Syntax.sigel = uu____55747;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_55746.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_55746.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_55746.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_55746.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____55779 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____55782 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____55789) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55822,(FStar_Util.Inl t,uu____55824),uu____55825)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55872,(FStar_Util.Inr c,uu____55874),uu____55875)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____55922 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55923,(FStar_Util.Inl t,uu____55925),uu____55926) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55973,(FStar_Util.Inr c,uu____55975),uu____55976) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56023 -> empty_set  in
          FStar_Util.set_union uu____55779 uu____55782  in
        let all_lb_univs =
          let uu____56027 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56043 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56043) empty_set)
             in
          FStar_All.pipe_right uu____56027 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56053 = s  in
        let uu____56054 =
          let uu____56055 =
            let uu____56062 =
              let uu____56063 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56075 = lb  in
                        let uu____56076 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56079 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56075.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56076;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56075.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56079;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56075.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56075.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56063)  in
            (uu____56062, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56055  in
        {
          FStar_Syntax_Syntax.sigel = uu____56054;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56053.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56053.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56053.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56053.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56088,fml) ->
        let uvs =
          let uu____56091 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56091 FStar_Util.set_elements  in
        let uu___1112_56096 = s  in
        let uu____56097 =
          let uu____56098 =
            let uu____56105 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56105)  in
          FStar_Syntax_Syntax.Sig_assume uu____56098  in
        {
          FStar_Syntax_Syntax.sigel = uu____56097;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56096.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56096.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56096.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56096.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56107,bs,c,flags) ->
        let uvs =
          let uu____56116 =
            let uu____56119 = bs_univnames bs  in
            let uu____56122 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56119 uu____56122  in
          FStar_All.pipe_right uu____56116 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56130 = s  in
        let uu____56131 =
          let uu____56132 =
            let uu____56145 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56146 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56145, uu____56146, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56132  in
        {
          FStar_Syntax_Syntax.sigel = uu____56131;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56130.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56130.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56130.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56130.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56149 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56157  ->
    match uu___433_56157 with
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
    | uu____56208 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56229 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56229)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56255 =
      let uu____56256 = unparen t  in uu____56256.FStar_Parser_AST.tm  in
    match uu____56255 with
    | FStar_Parser_AST.Wild  ->
        let uu____56262 =
          let uu____56263 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56263  in
        FStar_Util.Inr uu____56262
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____56276)) ->
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
             let uu____56367 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56367
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____56384 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56384
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____56400 =
               let uu____56406 =
                 let uu____56408 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____56408
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____56406)
                in
             FStar_Errors.raise_error uu____56400 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____56417 ->
        let rec aux t1 univargs =
          let uu____56454 =
            let uu____56455 = unparen t1  in uu____56455.FStar_Parser_AST.tm
             in
          match uu____56454 with
          | FStar_Parser_AST.App (t2,targ,uu____56463) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_56490  ->
                     match uu___434_56490 with
                     | FStar_Util.Inr uu____56497 -> true
                     | uu____56500 -> false) univargs
              then
                let uu____56508 =
                  let uu____56509 =
                    FStar_List.map
                      (fun uu___435_56519  ->
                         match uu___435_56519 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____56509  in
                FStar_Util.Inr uu____56508
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_56545  ->
                        match uu___436_56545 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____56555 -> failwith "impossible")
                     univargs
                    in
                 let uu____56559 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____56559)
          | uu____56575 ->
              let uu____56576 =
                let uu____56582 =
                  let uu____56584 =
                    let uu____56586 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____56586 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____56584  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56582)
                 in
              FStar_Errors.raise_error uu____56576 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____56601 ->
        let uu____56602 =
          let uu____56608 =
            let uu____56610 =
              let uu____56612 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____56612 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____56610  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56608)  in
        FStar_Errors.raise_error uu____56602 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____56653;_});
            FStar_Syntax_Syntax.pos = uu____56654;
            FStar_Syntax_Syntax.vars = uu____56655;_})::uu____56656
        ->
        let uu____56687 =
          let uu____56693 =
            let uu____56695 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____56695
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56693)  in
        FStar_Errors.raise_error uu____56687 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____56701 ->
        let uu____56720 =
          let uu____56726 =
            let uu____56728 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____56728
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56726)  in
        FStar_Errors.raise_error uu____56720 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____56741 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____56741) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____56769 = FStar_List.hd fields  in
        match uu____56769 with
        | (f,uu____56779) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____56791 =
                match uu____56791 with
                | (f',uu____56797) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____56799 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____56799
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
              (let uu____56809 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____56809);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57172 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57179 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57180 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57182,pats1) ->
              let aux out uu____57223 =
                match uu____57223 with
                | (p2,uu____57236) ->
                    let intersection =
                      let uu____57246 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57246 out  in
                    let uu____57249 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57249
                    then
                      let uu____57254 = pat_vars p2  in
                      FStar_Util.set_union out uu____57254
                    else
                      (let duplicate_bv =
                         let uu____57260 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57260  in
                       let uu____57263 =
                         let uu____57269 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____57269)
                          in
                       FStar_Errors.raise_error uu____57263 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____57293 = pat_vars p1  in
            FStar_All.pipe_right uu____57293 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____57321 =
                let uu____57323 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____57323  in
              if uu____57321
              then ()
              else
                (let nonlinear_vars =
                   let uu____57332 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____57332  in
                 let first_nonlinear_var =
                   let uu____57336 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____57336  in
                 let uu____57339 =
                   let uu____57345 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____57345)  in
                 FStar_Errors.raise_error uu____57339 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____57373 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____57373 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____57390 ->
            let uu____57393 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____57393 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____57544 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____57568 =
              let uu____57569 =
                let uu____57570 =
                  let uu____57577 =
                    let uu____57578 =
                      let uu____57584 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____57584, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____57578  in
                  (uu____57577, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____57570  in
              {
                FStar_Parser_AST.pat = uu____57569;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____57568
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____57604 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____57607 = aux loc env1 p2  in
              match uu____57607 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_57696 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_57701 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_57701.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_57701.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_57696.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_57703 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_57708 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_57708.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_57708.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_57703.FStar_Syntax_Syntax.p)
                        }
                    | uu____57709 when top -> p4
                    | uu____57710 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____57715 =
                    match binder with
                    | LetBinder uu____57736 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____57761 = close_fun env1 t  in
                          desugar_term env1 uu____57761  in
                        let x1 =
                          let uu___1380_57763 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_57763.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_57763.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____57715 with
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
            let uu____57831 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____57831, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____57845 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57845, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57869 = resolvex loc env1 x  in
            (match uu____57869 with
             | (loc1,env2,xbv) ->
                 let uu____57898 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57898, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57921 = resolvex loc env1 x  in
            (match uu____57921 with
             | (loc1,env2,xbv) ->
                 let uu____57950 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57950, [], imp))
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
            let uu____57965 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57965, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____57995;_},args)
            ->
            let uu____58001 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58062  ->
                     match uu____58062 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58143 = aux loc1 env2 arg  in
                         (match uu____58143 with
                          | (loc2,env3,uu____58190,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58001 with
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
                 let uu____58322 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____58322, annots, false))
        | FStar_Parser_AST.PatApp uu____58340 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____58371 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____58422  ->
                     match uu____58422 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____58483 = aux loc1 env2 pat  in
                         (match uu____58483 with
                          | (loc2,env3,uu____58525,pat1,ans,uu____58528) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____58371 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____58625 =
                     let uu____58628 =
                       let uu____58635 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____58635  in
                     let uu____58636 =
                       let uu____58637 =
                         let uu____58651 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____58651, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____58637  in
                     FStar_All.pipe_left uu____58628 uu____58636  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____58685 =
                            let uu____58686 =
                              let uu____58700 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____58700, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____58686  in
                          FStar_All.pipe_left (pos_r r) uu____58685) pats1
                     uu____58625
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
            let uu____58758 =
              FStar_List.fold_left
                (fun uu____58818  ->
                   fun p2  ->
                     match uu____58818 with
                     | (loc1,env2,annots,pats) ->
                         let uu____58900 = aux loc1 env2 p2  in
                         (match uu____58900 with
                          | (loc2,env3,uu____58947,pat,ans,uu____58950) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____58758 with
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
                   | uu____59116 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59119 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59119, annots, false))
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
                   (fun uu____59200  ->
                      match uu____59200 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59230  ->
                      match uu____59230 with
                      | (f,uu____59236) ->
                          let uu____59237 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59263  ->
                                    match uu____59263 with
                                    | (g,uu____59270) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59237 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____59276,p2) ->
                               p2)))
               in
            let app =
              let uu____59283 =
                let uu____59284 =
                  let uu____59291 =
                    let uu____59292 =
                      let uu____59293 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____59293  in
                    FStar_Parser_AST.mk_pattern uu____59292
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____59291, args)  in
                FStar_Parser_AST.PatApp uu____59284  in
              FStar_Parser_AST.mk_pattern uu____59283
                p1.FStar_Parser_AST.prange
               in
            let uu____59296 = aux loc env1 app  in
            (match uu____59296 with
             | (env2,e,b,p2,annots,uu____59342) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____59382 =
                         let uu____59383 =
                           let uu____59397 =
                             let uu___1528_59398 = fv  in
                             let uu____59399 =
                               let uu____59402 =
                                 let uu____59403 =
                                   let uu____59410 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____59410)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____59403
                                  in
                               FStar_Pervasives_Native.Some uu____59402  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_59398.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_59398.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____59399
                             }  in
                           (uu____59397, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____59383  in
                       FStar_All.pipe_left pos uu____59382
                   | uu____59436 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____59522 = aux' true loc env1 p2  in
            (match uu____59522 with
             | (loc1,env2,var,p3,ans,uu____59566) ->
                 let uu____59581 =
                   FStar_List.fold_left
                     (fun uu____59630  ->
                        fun p4  ->
                          match uu____59630 with
                          | (loc2,env3,ps1) ->
                              let uu____59695 = aux' true loc2 env3 p4  in
                              (match uu____59695 with
                               | (loc3,env4,uu____59736,p5,ans1,uu____59739)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____59581 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____59900 ->
            let uu____59901 = aux' true loc env1 p1  in
            (match uu____59901 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____59998 = aux_maybe_or env p  in
      match uu____59998 with
      | (env1,b,pats) ->
          ((let uu____60053 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60053
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
          let uu____60126 =
            let uu____60127 =
              let uu____60138 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60138, (ty, tacopt))  in
            LetBinder uu____60127  in
          (env, uu____60126, [])  in
        let op_to_ident x =
          let uu____60155 =
            let uu____60161 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60161, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60155  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60183 = op_to_ident x  in
              mklet uu____60183 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60185) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60191;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60207 = op_to_ident x  in
              let uu____60208 = desugar_term env t  in
              mklet uu____60207 uu____60208 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60210);
                 FStar_Parser_AST.prange = uu____60211;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60231 = desugar_term env t  in
              mklet x uu____60231 tacopt1
          | uu____60232 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60245 = desugar_data_pat env p  in
           match uu____60245 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____60274;
                      FStar_Syntax_Syntax.p = uu____60275;_},uu____60276)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____60289;
                      FStar_Syntax_Syntax.p = uu____60290;_},uu____60291)::[]
                     -> []
                 | uu____60304 -> p1  in
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
  fun uu____60312  ->
    fun env  ->
      fun pat  ->
        let uu____60316 = desugar_data_pat env pat  in
        match uu____60316 with | (env1,uu____60332,pat1) -> (env1, pat1)

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
      let uu____60354 = desugar_term_aq env e  in
      match uu____60354 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____60373 = desugar_typ_aq env e  in
      match uu____60373 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____60383  ->
        fun range  ->
          match uu____60383 with
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
              ((let uu____60405 =
                  let uu____60407 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____60407  in
                if uu____60405
                then
                  let uu____60410 =
                    let uu____60416 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____60416)  in
                  FStar_Errors.log_issue range uu____60410
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
                  let uu____60437 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____60437 range  in
                let lid1 =
                  let uu____60441 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____60441 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____60451 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____60451 range  in
                           let private_fv =
                             let uu____60453 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____60453 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_60454 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_60454.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_60454.FStar_Syntax_Syntax.vars)
                           }
                       | uu____60455 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60459 =
                        let uu____60465 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____60465)
                         in
                      FStar_Errors.raise_error uu____60459 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____60485 =
                  let uu____60492 =
                    let uu____60493 =
                      let uu____60510 =
                        let uu____60521 =
                          let uu____60530 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____60530)  in
                        [uu____60521]  in
                      (lid1, uu____60510)  in
                    FStar_Syntax_Syntax.Tm_app uu____60493  in
                  FStar_Syntax_Syntax.mk uu____60492  in
                uu____60485 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____60578 =
          let uu____60579 = unparen t  in uu____60579.FStar_Parser_AST.tm  in
        match uu____60578 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____60580; FStar_Ident.ident = uu____60581;
              FStar_Ident.nsstr = uu____60582; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____60587 ->
            let uu____60588 =
              let uu____60594 =
                let uu____60596 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____60596  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____60594)  in
            FStar_Errors.raise_error uu____60588 t.FStar_Parser_AST.range
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
          let uu___1725_60683 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_60683.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_60683.FStar_Syntax_Syntax.vars)
          }  in
        let uu____60686 =
          let uu____60687 = unparen top  in uu____60687.FStar_Parser_AST.tm
           in
        match uu____60686 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____60692 ->
            let uu____60701 = desugar_formula env top  in
            (uu____60701, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____60710 = desugar_formula env t  in (uu____60710, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____60719 = desugar_formula env t  in (uu____60719, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____60746 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____60746, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____60748 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____60748, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____60757 =
                let uu____60758 =
                  let uu____60765 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____60765, args)  in
                FStar_Parser_AST.Op uu____60758  in
              FStar_Parser_AST.mk_term uu____60757 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____60770 =
              let uu____60771 =
                let uu____60772 =
                  let uu____60779 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____60779, [e])  in
                FStar_Parser_AST.Op uu____60772  in
              FStar_Parser_AST.mk_term uu____60771 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____60770
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____60791 = FStar_Ident.text_of_id op_star  in
             uu____60791 = "*") &&
              (let uu____60796 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____60796 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____60813;_},t1::t2::[])
                  when
                  let uu____60819 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____60819 FStar_Option.isNone ->
                  let uu____60826 = flatten1 t1  in
                  FStar_List.append uu____60826 [t2]
              | uu____60829 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_60834 = top  in
              let uu____60835 =
                let uu____60836 =
                  let uu____60847 =
                    FStar_List.map (fun _60858  -> FStar_Util.Inr _60858)
                      terms
                     in
                  (uu____60847, rhs)  in
                FStar_Parser_AST.Sum uu____60836  in
              {
                FStar_Parser_AST.tm = uu____60835;
                FStar_Parser_AST.range =
                  (uu___1773_60834.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_60834.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____60866 =
              let uu____60867 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____60867  in
            (uu____60866, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____60873 =
              let uu____60879 =
                let uu____60881 =
                  let uu____60883 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____60883 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____60881  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____60879)
               in
            FStar_Errors.raise_error uu____60873 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____60898 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____60898 with
             | FStar_Pervasives_Native.None  ->
                 let uu____60905 =
                   let uu____60911 =
                     let uu____60913 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____60913
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____60911)
                    in
                 FStar_Errors.raise_error uu____60905
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____60928 =
                     let uu____60953 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61015 = desugar_term_aq env t  in
                               match uu____61015 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____60953 FStar_List.unzip  in
                   (match uu____60928 with
                    | (args1,aqs) ->
                        let uu____61148 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61148, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61165)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61182 =
              let uu___1802_61183 = top  in
              let uu____61184 =
                let uu____61185 =
                  let uu____61192 =
                    let uu___1804_61193 = top  in
                    let uu____61194 =
                      let uu____61195 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61195  in
                    {
                      FStar_Parser_AST.tm = uu____61194;
                      FStar_Parser_AST.range =
                        (uu___1804_61193.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61193.FStar_Parser_AST.level)
                    }  in
                  (uu____61192, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61185  in
              {
                FStar_Parser_AST.tm = uu____61184;
                FStar_Parser_AST.range =
                  (uu___1802_61183.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61183.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61182
        | FStar_Parser_AST.Construct (n1,(a,uu____61203)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61223 =
                let uu___1814_61224 = top  in
                let uu____61225 =
                  let uu____61226 =
                    let uu____61233 =
                      let uu___1816_61234 = top  in
                      let uu____61235 =
                        let uu____61236 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61236  in
                      {
                        FStar_Parser_AST.tm = uu____61235;
                        FStar_Parser_AST.range =
                          (uu___1816_61234.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61234.FStar_Parser_AST.level)
                      }  in
                    (uu____61233, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61226  in
                {
                  FStar_Parser_AST.tm = uu____61225;
                  FStar_Parser_AST.range =
                    (uu___1814_61224.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61224.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61223))
        | FStar_Parser_AST.Construct (n1,(a,uu____61244)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61261 =
              let uu___1825_61262 = top  in
              let uu____61263 =
                let uu____61264 =
                  let uu____61271 =
                    let uu___1827_61272 = top  in
                    let uu____61273 =
                      let uu____61274 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61274  in
                    {
                      FStar_Parser_AST.tm = uu____61273;
                      FStar_Parser_AST.range =
                        (uu___1827_61272.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_61272.FStar_Parser_AST.level)
                    }  in
                  (uu____61271, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61264  in
              {
                FStar_Parser_AST.tm = uu____61263;
                FStar_Parser_AST.range =
                  (uu___1825_61262.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61262.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61261
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61280; FStar_Ident.ident = uu____61281;
              FStar_Ident.nsstr = uu____61282; FStar_Ident.str = "Type0";_}
            ->
            let uu____61287 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____61287, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61288; FStar_Ident.ident = uu____61289;
              FStar_Ident.nsstr = uu____61290; FStar_Ident.str = "Type";_}
            ->
            let uu____61295 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____61295, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____61296; FStar_Ident.ident = uu____61297;
               FStar_Ident.nsstr = uu____61298; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____61318 =
              let uu____61319 =
                let uu____61320 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____61320  in
              mk1 uu____61319  in
            (uu____61318, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61321; FStar_Ident.ident = uu____61322;
              FStar_Ident.nsstr = uu____61323; FStar_Ident.str = "Effect";_}
            ->
            let uu____61328 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____61328, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61329; FStar_Ident.ident = uu____61330;
              FStar_Ident.nsstr = uu____61331; FStar_Ident.str = "True";_}
            ->
            let uu____61336 =
              let uu____61337 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61337
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61336, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61338; FStar_Ident.ident = uu____61339;
              FStar_Ident.nsstr = uu____61340; FStar_Ident.str = "False";_}
            ->
            let uu____61345 =
              let uu____61346 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61346
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61345, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____61349;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____61352 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____61352 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____61361 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____61361, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____61363 =
                    let uu____61365 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____61365 txt
                     in
                  failwith uu____61363))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61374 = desugar_name mk1 setpos env true l  in
              (uu____61374, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61383 = desugar_name mk1 setpos env true l  in
              (uu____61383, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____61401 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____61401 with
                | FStar_Pervasives_Native.Some uu____61411 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____61419 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____61419 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____61437 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____61458 =
                    let uu____61459 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____61459  in
                  (uu____61458, noaqs)
              | uu____61465 ->
                  let uu____61473 =
                    let uu____61479 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____61479)  in
                  FStar_Errors.raise_error uu____61473
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____61489 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____61489 with
              | FStar_Pervasives_Native.None  ->
                  let uu____61496 =
                    let uu____61502 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____61502)
                     in
                  FStar_Errors.raise_error uu____61496
                    top.FStar_Parser_AST.range
              | uu____61510 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____61514 = desugar_name mk1 setpos env true lid'  in
                  (uu____61514, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61536 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____61536 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____61555 ->
                       let uu____61562 =
                         FStar_Util.take
                           (fun uu____61586  ->
                              match uu____61586 with
                              | (uu____61592,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____61562 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____61637 =
                              let uu____61662 =
                                FStar_List.map
                                  (fun uu____61705  ->
                                     match uu____61705 with
                                     | (t,imp) ->
                                         let uu____61722 =
                                           desugar_term_aq env t  in
                                         (match uu____61722 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____61662
                                FStar_List.unzip
                               in
                            (match uu____61637 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____61865 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____61865, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____61884 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____61884 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____61895 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_61923  ->
                 match uu___437_61923 with
                 | FStar_Util.Inr uu____61929 -> true
                 | uu____61931 -> false) binders
            ->
            let terms =
              let uu____61940 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_61957  ->
                        match uu___438_61957 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____61963 -> failwith "Impossible"))
                 in
              FStar_List.append uu____61940 [t]  in
            let uu____61965 =
              let uu____61990 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62047 = desugar_typ_aq env t1  in
                        match uu____62047 with
                        | (t',aq) ->
                            let uu____62058 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62058, aq)))
                 in
              FStar_All.pipe_right uu____61990 FStar_List.unzip  in
            (match uu____61965 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62168 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62168
                    in
                 let uu____62177 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62177, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62204 =
              let uu____62221 =
                let uu____62228 =
                  let uu____62235 =
                    FStar_All.pipe_left
                      (fun _62244  -> FStar_Util.Inl _62244)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62235]  in
                FStar_List.append binders uu____62228  in
              FStar_List.fold_left
                (fun uu____62289  ->
                   fun b  ->
                     match uu____62289 with
                     | (env1,tparams,typs) ->
                         let uu____62350 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____62365 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____62365)
                            in
                         (match uu____62350 with
                          | (xopt,t1) ->
                              let uu____62390 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____62399 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____62399)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____62390 with
                               | (env2,x) ->
                                   let uu____62419 =
                                     let uu____62422 =
                                       let uu____62425 =
                                         let uu____62426 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____62426
                                          in
                                       [uu____62425]  in
                                     FStar_List.append typs uu____62422  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_62452 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_62452.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_62452.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____62419)))) (env, [], [])
                uu____62221
               in
            (match uu____62204 with
             | (env1,uu____62480,targs) ->
                 let tup =
                   let uu____62503 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____62503
                    in
                 let uu____62504 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____62504, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____62523 = uncurry binders t  in
            (match uu____62523 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_62567 =
                   match uu___439_62567 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____62584 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____62584
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____62608 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____62608 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____62641 = aux env [] bs  in (uu____62641, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____62650 = desugar_binder env b  in
            (match uu____62650 with
             | (FStar_Pervasives_Native.None ,uu____62661) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____62676 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____62676 with
                  | ((x,uu____62692),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____62705 =
                        let uu____62706 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____62706  in
                      (uu____62705, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____62785 = FStar_Util.set_is_empty i  in
                    if uu____62785
                    then
                      let uu____62790 = FStar_Util.set_union acc set1  in
                      aux uu____62790 sets2
                    else
                      (let uu____62795 =
                         let uu____62796 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____62796  in
                       FStar_Pervasives_Native.Some uu____62795)
                 in
              let uu____62799 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____62799 sets  in
            ((let uu____62803 = check_disjoint bvss  in
              match uu____62803 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____62807 =
                    let uu____62813 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____62813)
                     in
                  let uu____62817 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____62807 uu____62817);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____62825 =
                FStar_List.fold_left
                  (fun uu____62845  ->
                     fun pat  ->
                       match uu____62845 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____62871,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____62881 =
                                  let uu____62884 = free_type_vars env1 t  in
                                  FStar_List.append uu____62884 ftvs  in
                                (env1, uu____62881)
                            | FStar_Parser_AST.PatAscribed
                                (uu____62889,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____62900 =
                                  let uu____62903 = free_type_vars env1 t  in
                                  let uu____62906 =
                                    let uu____62909 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____62909 ftvs  in
                                  FStar_List.append uu____62903 uu____62906
                                   in
                                (env1, uu____62900)
                            | uu____62914 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____62825 with
              | (uu____62923,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____62935 =
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
                    FStar_List.append uu____62935 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_62992 =
                    match uu___440_62992 with
                    | [] ->
                        let uu____63019 = desugar_term_aq env1 body  in
                        (match uu____63019 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63056 =
                                       let uu____63057 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63057
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63056
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
                             let uu____63126 =
                               let uu____63129 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63129  in
                             (uu____63126, aq))
                    | p::rest ->
                        let uu____63144 = desugar_binding_pat env1 p  in
                        (match uu____63144 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63178)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63193 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63202 =
                               match b with
                               | LetBinder uu____63243 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____63312) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____63366 =
                                           let uu____63375 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____63375, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____63366
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____63437,uu____63438) ->
                                              let tup2 =
                                                let uu____63440 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63440
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63445 =
                                                  let uu____63452 =
                                                    let uu____63453 =
                                                      let uu____63470 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____63473 =
                                                        let uu____63484 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____63493 =
                                                          let uu____63504 =
                                                            let uu____63513 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____63513
                                                             in
                                                          [uu____63504]  in
                                                        uu____63484 ::
                                                          uu____63493
                                                         in
                                                      (uu____63470,
                                                        uu____63473)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____63453
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____63452
                                                   in
                                                uu____63445
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____63561 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____63561
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____63612,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____63614,pats)) ->
                                              let tupn =
                                                let uu____63659 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63659
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63672 =
                                                  let uu____63673 =
                                                    let uu____63690 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____63693 =
                                                      let uu____63704 =
                                                        let uu____63715 =
                                                          let uu____63724 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____63724
                                                           in
                                                        [uu____63715]  in
                                                      FStar_List.append args
                                                        uu____63704
                                                       in
                                                    (uu____63690,
                                                      uu____63693)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____63673
                                                   in
                                                mk1 uu____63672  in
                                              let p2 =
                                                let uu____63772 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____63772
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____63819 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63202 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____63913,uu____63914,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____63936 =
                let uu____63937 = unparen e  in
                uu____63937.FStar_Parser_AST.tm  in
              match uu____63936 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____63947 ->
                  let uu____63948 = desugar_term_aq env e  in
                  (match uu____63948 with
                   | (head1,aq) ->
                       let uu____63961 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____63961, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____63968 ->
            let rec aux args aqs e =
              let uu____64045 =
                let uu____64046 = unparen e  in
                uu____64046.FStar_Parser_AST.tm  in
              match uu____64045 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64064 = desugar_term_aq env t  in
                  (match uu____64064 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64112 ->
                  let uu____64113 = desugar_term_aq env e  in
                  (match uu____64113 with
                   | (head1,aq) ->
                       let uu____64134 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64134, (join_aqs (aq :: aqs))))
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
            let uu____64197 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64197
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
            let uu____64249 = desugar_term_aq env t  in
            (match uu____64249 with
             | (tm,s) ->
                 let uu____64260 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64260, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____64266 =
              let uu____64279 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____64279 then desugar_typ_aq else desugar_term_aq  in
            uu____64266 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____64338 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____64481  ->
                        match uu____64481 with
                        | (attr_opt,(p,def)) ->
                            let uu____64539 = is_app_pattern p  in
                            if uu____64539
                            then
                              let uu____64572 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____64572, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____64655 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____64655, def1)
                               | uu____64700 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____64738);
                                           FStar_Parser_AST.prange =
                                             uu____64739;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____64788 =
                                            let uu____64809 =
                                              let uu____64814 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64814  in
                                            (uu____64809, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____64788, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____64906) ->
                                        if top_level
                                        then
                                          let uu____64942 =
                                            let uu____64963 =
                                              let uu____64968 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64968  in
                                            (uu____64963, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____64942, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65059 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65092 =
                FStar_List.fold_left
                  (fun uu____65165  ->
                     fun uu____65166  ->
                       match (uu____65165, uu____65166) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____65274,uu____65275),uu____65276))
                           ->
                           let uu____65393 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____65419 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____65419 with
                                  | (env2,xx) ->
                                      let uu____65438 =
                                        let uu____65441 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____65441 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____65438))
                             | FStar_Util.Inr l ->
                                 let uu____65449 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____65449, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____65393 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65092 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____65597 =
                    match uu____65597 with
                    | (attrs_opt,(uu____65633,args,result_t),def) ->
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
                                let uu____65721 = is_comp_type env1 t  in
                                if uu____65721
                                then
                                  ((let uu____65725 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____65735 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____65735))
                                       in
                                    match uu____65725 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____65742 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____65745 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____65745))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____65742
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
                          | uu____65756 ->
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
                              let uu____65771 =
                                let uu____65772 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____65772
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____65771
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
                  let uu____65853 = desugar_term_aq env' body  in
                  (match uu____65853 with
                   | (body1,aq) ->
                       let uu____65866 =
                         let uu____65869 =
                           let uu____65870 =
                             let uu____65884 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____65884)  in
                           FStar_Syntax_Syntax.Tm_let uu____65870  in
                         FStar_All.pipe_left mk1 uu____65869  in
                       (uu____65866, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____65959 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____65959 with
              | (env1,binder,pat1) ->
                  let uu____65981 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66007 = desugar_term_aq env1 t2  in
                        (match uu____66007 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66021 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66021
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66022 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66022, aq))
                    | LocalBinder (x,uu____66055) ->
                        let uu____66056 = desugar_term_aq env1 t2  in
                        (match uu____66056 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66070;
                                    FStar_Syntax_Syntax.p = uu____66071;_},uu____66072)::[]
                                   -> body1
                               | uu____66085 ->
                                   let uu____66088 =
                                     let uu____66095 =
                                       let uu____66096 =
                                         let uu____66119 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66122 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66119, uu____66122)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66096
                                        in
                                     FStar_Syntax_Syntax.mk uu____66095  in
                                   uu____66088 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66159 =
                               let uu____66162 =
                                 let uu____66163 =
                                   let uu____66177 =
                                     let uu____66180 =
                                       let uu____66181 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66181]  in
                                     FStar_Syntax_Subst.close uu____66180
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66177)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66163  in
                               FStar_All.pipe_left mk1 uu____66162  in
                             (uu____66159, aq))
                     in
                  (match uu____65981 with | (tm,aq) -> (tm, aq))
               in
            let uu____66243 = FStar_List.hd lbs  in
            (match uu____66243 with
             | (attrs,(head_pat,defn)) ->
                 let uu____66287 = is_rec || (is_app_pattern head_pat)  in
                 if uu____66287
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____66303 =
                let uu____66304 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____66304  in
              mk1 uu____66303  in
            let uu____66305 = desugar_term_aq env t1  in
            (match uu____66305 with
             | (t1',aq1) ->
                 let uu____66316 = desugar_term_aq env t2  in
                 (match uu____66316 with
                  | (t2',aq2) ->
                      let uu____66327 = desugar_term_aq env t3  in
                      (match uu____66327 with
                       | (t3',aq3) ->
                           let uu____66338 =
                             let uu____66339 =
                               let uu____66340 =
                                 let uu____66363 =
                                   let uu____66380 =
                                     let uu____66395 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____66395,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____66409 =
                                     let uu____66426 =
                                       let uu____66441 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____66441,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____66426]  in
                                   uu____66380 :: uu____66409  in
                                 (t1', uu____66363)  in
                               FStar_Syntax_Syntax.Tm_match uu____66340  in
                             mk1 uu____66339  in
                           (uu____66338, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____66637 =
              match uu____66637 with
              | (pat,wopt,b) ->
                  let uu____66659 = desugar_match_pat env pat  in
                  (match uu____66659 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____66690 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____66690
                          in
                       let uu____66695 = desugar_term_aq env1 b  in
                       (match uu____66695 with
                        | (b1,aq) ->
                            let uu____66708 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____66708, aq)))
               in
            let uu____66713 = desugar_term_aq env e  in
            (match uu____66713 with
             | (e1,aq) ->
                 let uu____66724 =
                   let uu____66755 =
                     let uu____66788 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____66788 FStar_List.unzip  in
                   FStar_All.pipe_right uu____66755
                     (fun uu____67006  ->
                        match uu____67006 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____66724 with
                  | (brs,aqs) ->
                      let uu____67225 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67225, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67259 =
              let uu____67280 = is_comp_type env t  in
              if uu____67280
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____67335 = desugar_term_aq env t  in
                 match uu____67335 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67259 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____67427 = desugar_term_aq env e  in
                 (match uu____67427 with
                  | (e1,aq) ->
                      let uu____67438 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____67438, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____67477,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____67520 = FStar_List.hd fields  in
              match uu____67520 with | (f,uu____67532) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____67578  ->
                        match uu____67578 with
                        | (g,uu____67585) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____67592,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____67606 =
                         let uu____67612 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____67612)
                          in
                       FStar_Errors.raise_error uu____67606
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
                  let uu____67623 =
                    let uu____67634 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____67665  ->
                              match uu____67665 with
                              | (f,uu____67675) ->
                                  let uu____67676 =
                                    let uu____67677 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____67677
                                     in
                                  (uu____67676, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____67634)  in
                  FStar_Parser_AST.Construct uu____67623
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____67695 =
                      let uu____67696 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____67696  in
                    FStar_Parser_AST.mk_term uu____67695
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____67698 =
                      let uu____67711 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____67741  ->
                                match uu____67741 with
                                | (f,uu____67751) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____67711)  in
                    FStar_Parser_AST.Record uu____67698  in
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
            let uu____67811 = desugar_term_aq env recterm1  in
            (match uu____67811 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____67827;
                         FStar_Syntax_Syntax.vars = uu____67828;_},args)
                      ->
                      let uu____67854 =
                        let uu____67855 =
                          let uu____67856 =
                            let uu____67873 =
                              let uu____67876 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____67877 =
                                let uu____67880 =
                                  let uu____67881 =
                                    let uu____67888 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____67888)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____67881
                                   in
                                FStar_Pervasives_Native.Some uu____67880  in
                              FStar_Syntax_Syntax.fvar uu____67876
                                FStar_Syntax_Syntax.delta_constant
                                uu____67877
                               in
                            (uu____67873, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____67856  in
                        FStar_All.pipe_left mk1 uu____67855  in
                      (uu____67854, s)
                  | uu____67917 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____67921 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____67921 with
              | (constrname,is_rec) ->
                  let uu____67940 = desugar_term_aq env e  in
                  (match uu____67940 with
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
                       let uu____67960 =
                         let uu____67961 =
                           let uu____67962 =
                             let uu____67979 =
                               let uu____67982 =
                                 let uu____67983 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____67983
                                  in
                               FStar_Syntax_Syntax.fvar uu____67982
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____67985 =
                               let uu____67996 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____67996]  in
                             (uu____67979, uu____67985)  in
                           FStar_Syntax_Syntax.Tm_app uu____67962  in
                         FStar_All.pipe_left mk1 uu____67961  in
                       (uu____67960, s))))
        | FStar_Parser_AST.NamedTyp (uu____68033,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68043 =
              let uu____68044 = FStar_Syntax_Subst.compress tm  in
              uu____68044.FStar_Syntax_Syntax.n  in
            (match uu____68043 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68052 =
                   let uu___2520_68053 =
                     let uu____68054 =
                       let uu____68056 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68056  in
                     FStar_Syntax_Util.exp_string uu____68054  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68053.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68053.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68052, noaqs)
             | uu____68057 ->
                 let uu____68058 =
                   let uu____68064 =
                     let uu____68066 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68066
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68064)  in
                 FStar_Errors.raise_error uu____68058
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68075 = desugar_term_aq env e  in
            (match uu____68075 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68087 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68087, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68092 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68093 =
              let uu____68094 =
                let uu____68101 = desugar_term env e  in (bv, uu____68101)
                 in
              [uu____68094]  in
            (uu____68092, uu____68093)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68126 =
              let uu____68127 =
                let uu____68128 =
                  let uu____68135 = desugar_term env e  in (uu____68135, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68128  in
              FStar_All.pipe_left mk1 uu____68127  in
            (uu____68126, noaqs)
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
              let uu____68164 =
                let uu____68165 =
                  let uu____68172 =
                    let uu____68173 =
                      let uu____68174 =
                        let uu____68183 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68196 =
                          let uu____68197 =
                            let uu____68198 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68198  in
                          FStar_Parser_AST.mk_term uu____68197
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68183, uu____68196,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68174  in
                    FStar_Parser_AST.mk_term uu____68173
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68172)  in
                FStar_Parser_AST.Abs uu____68165  in
              FStar_Parser_AST.mk_term uu____68164
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
                   fun uu____68244  ->
                     match uu____68244 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68248 =
                           let uu____68255 =
                             let uu____68260 = eta_and_annot rel2  in
                             (uu____68260, FStar_Parser_AST.Nothing)  in
                           let uu____68261 =
                             let uu____68268 =
                               let uu____68275 =
                                 let uu____68280 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____68280, FStar_Parser_AST.Nothing)  in
                               let uu____68281 =
                                 let uu____68288 =
                                   let uu____68293 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____68293, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____68288]  in
                               uu____68275 :: uu____68281  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____68268
                              in
                           uu____68255 :: uu____68261  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68248
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____68315 =
                let uu____68322 =
                  let uu____68327 = FStar_Parser_AST.thunk e1  in
                  (uu____68327, FStar_Parser_AST.Nothing)  in
                [uu____68322]  in
              FStar_Parser_AST.mkApp finish1 uu____68315
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____68336 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____68337 = desugar_formula env top  in
            (uu____68337, noaqs)
        | uu____68338 ->
            let uu____68339 =
              let uu____68345 =
                let uu____68347 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____68347  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____68345)  in
            FStar_Errors.raise_error uu____68339 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____68357 -> false
    | uu____68367 -> true

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
           (fun uu____68405  ->
              match uu____68405 with
              | (a,imp) ->
                  let uu____68418 = desugar_term env a  in
                  arg_withimp_e imp uu____68418))

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
          let is_requires uu____68455 =
            match uu____68455 with
            | (t1,uu____68462) ->
                let uu____68463 =
                  let uu____68464 = unparen t1  in
                  uu____68464.FStar_Parser_AST.tm  in
                (match uu____68463 with
                 | FStar_Parser_AST.Requires uu____68466 -> true
                 | uu____68475 -> false)
             in
          let is_ensures uu____68487 =
            match uu____68487 with
            | (t1,uu____68494) ->
                let uu____68495 =
                  let uu____68496 = unparen t1  in
                  uu____68496.FStar_Parser_AST.tm  in
                (match uu____68495 with
                 | FStar_Parser_AST.Ensures uu____68498 -> true
                 | uu____68507 -> false)
             in
          let is_app head1 uu____68525 =
            match uu____68525 with
            | (t1,uu____68533) ->
                let uu____68534 =
                  let uu____68535 = unparen t1  in
                  uu____68535.FStar_Parser_AST.tm  in
                (match uu____68534 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____68538;
                        FStar_Parser_AST.level = uu____68539;_},uu____68540,uu____68541)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____68543 -> false)
             in
          let is_smt_pat uu____68555 =
            match uu____68555 with
            | (t1,uu____68562) ->
                let uu____68563 =
                  let uu____68564 = unparen t1  in
                  uu____68564.FStar_Parser_AST.tm  in
                (match uu____68563 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____68568);
                               FStar_Parser_AST.range = uu____68569;
                               FStar_Parser_AST.level = uu____68570;_},uu____68571)::uu____68572::[])
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
                               FStar_Parser_AST.range = uu____68621;
                               FStar_Parser_AST.level = uu____68622;_},uu____68623)::uu____68624::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____68657 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____68692 = head_and_args t1  in
            match uu____68692 with
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
                     let thunk_ens uu____68785 =
                       match uu____68785 with
                       | (e,i) ->
                           let uu____68796 = FStar_Parser_AST.thunk e  in
                           (uu____68796, i)
                        in
                     let fail_lemma uu____68808 =
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
                           let uu____68914 =
                             let uu____68921 =
                               let uu____68928 = thunk_ens ens  in
                               [uu____68928; nil_pat]  in
                             req_true :: uu____68921  in
                           unit_tm :: uu____68914
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____68975 =
                             let uu____68982 =
                               let uu____68989 = thunk_ens ens  in
                               [uu____68989; nil_pat]  in
                             req :: uu____68982  in
                           unit_tm :: uu____68975
                       | ens::smtpat::[] when
                           (((let uu____69038 = is_requires ens  in
                              Prims.op_Negation uu____69038) &&
                               (let uu____69041 = is_smt_pat ens  in
                                Prims.op_Negation uu____69041))
                              &&
                              (let uu____69044 = is_decreases ens  in
                               Prims.op_Negation uu____69044))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69046 =
                             let uu____69053 =
                               let uu____69060 = thunk_ens ens  in
                               [uu____69060; smtpat]  in
                             req_true :: uu____69053  in
                           unit_tm :: uu____69046
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69107 =
                             let uu____69114 =
                               let uu____69121 = thunk_ens ens  in
                               [uu____69121; nil_pat; dec]  in
                             req_true :: uu____69114  in
                           unit_tm :: uu____69107
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69181 =
                             let uu____69188 =
                               let uu____69195 = thunk_ens ens  in
                               [uu____69195; smtpat; dec]  in
                             req_true :: uu____69188  in
                           unit_tm :: uu____69181
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69255 =
                             let uu____69262 =
                               let uu____69269 = thunk_ens ens  in
                               [uu____69269; nil_pat; dec]  in
                             req :: uu____69262  in
                           unit_tm :: uu____69255
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69329 =
                             let uu____69336 =
                               let uu____69343 = thunk_ens ens  in
                               [uu____69343; smtpat]  in
                             req :: uu____69336  in
                           unit_tm :: uu____69329
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____69408 =
                             let uu____69415 =
                               let uu____69422 = thunk_ens ens  in
                               [uu____69422; dec; smtpat]  in
                             req :: uu____69415  in
                           unit_tm :: uu____69408
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____69484 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____69484, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69512 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69512
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____69515 =
                       let uu____69522 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69522, [])  in
                     (uu____69515, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69540 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69540
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____69543 =
                       let uu____69550 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69550, [])  in
                     (uu____69543, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____69572 =
                       let uu____69579 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69579, [])  in
                     (uu____69572, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69602 when allow_type_promotion ->
                     let default_effect =
                       let uu____69604 = FStar_Options.ml_ish ()  in
                       if uu____69604
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____69610 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____69610
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____69617 =
                       let uu____69624 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69624, [])  in
                     (uu____69617, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69647 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____69666 = pre_process_comp_typ t  in
          match uu____69666 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____69718 =
                    let uu____69724 =
                      let uu____69726 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____69726
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____69724)
                     in
                  fail1 uu____69718)
               else ();
               (let is_universe uu____69742 =
                  match uu____69742 with
                  | (uu____69748,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____69750 = FStar_Util.take is_universe args  in
                match uu____69750 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____69809  ->
                           match uu____69809 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____69816 =
                      let uu____69831 = FStar_List.hd args1  in
                      let uu____69840 = FStar_List.tl args1  in
                      (uu____69831, uu____69840)  in
                    (match uu____69816 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____69895 =
                           let is_decrease uu____69934 =
                             match uu____69934 with
                             | (t1,uu____69945) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____69956;
                                         FStar_Syntax_Syntax.vars =
                                           uu____69957;_},uu____69958::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____69997 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____69895 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70114  ->
                                        match uu____70114 with
                                        | (t1,uu____70124) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70133,(arg,uu____70135)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70174 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70195 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70207 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70207
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70214 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70214
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70224 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70224
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70231 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70231
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70238 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70238
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70245 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70245
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____70266 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70266
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
                                                    let uu____70357 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____70357
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
                                              | uu____70378 -> pat  in
                                            let uu____70379 =
                                              let uu____70390 =
                                                let uu____70401 =
                                                  let uu____70410 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____70410, aq)  in
                                                [uu____70401]  in
                                              ens :: uu____70390  in
                                            req :: uu____70379
                                        | uu____70451 -> rest2
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
        | uu____70483 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_70505 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_70505.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_70505.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_70547 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_70547.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_70547.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_70547.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____70610 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____70610)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____70623 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____70623 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_70633 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_70633.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_70633.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____70659 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____70673 =
                     let uu____70676 =
                       let uu____70677 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____70677]  in
                     no_annot_abs uu____70676 body2  in
                   FStar_All.pipe_left setpos uu____70673  in
                 let uu____70698 =
                   let uu____70699 =
                     let uu____70716 =
                       let uu____70719 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____70719
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____70721 =
                       let uu____70732 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____70732]  in
                     (uu____70716, uu____70721)  in
                   FStar_Syntax_Syntax.Tm_app uu____70699  in
                 FStar_All.pipe_left mk1 uu____70698)
        | uu____70771 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____70852 = q (rest, pats, body)  in
              let uu____70859 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____70852 uu____70859
                FStar_Parser_AST.Formula
               in
            let uu____70860 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____70860 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____70869 -> failwith "impossible"  in
      let uu____70873 =
        let uu____70874 = unparen f  in uu____70874.FStar_Parser_AST.tm  in
      match uu____70873 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____70887,uu____70888) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____70900,uu____70901) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70933 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____70933
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70969 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____70969
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71013 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71018 =
        FStar_List.fold_left
          (fun uu____71051  ->
             fun b  ->
               match uu____71051 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71095 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71095.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71095.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71095.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71110 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71110 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71128 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71128.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71128.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71129 =
                               let uu____71136 =
                                 let uu____71141 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71141)  in
                               uu____71136 :: out  in
                             (env2, uu____71129))
                    | uu____71152 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71018 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71225 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71225)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71230 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71230)
      | FStar_Parser_AST.TVariable x ->
          let uu____71234 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71234)
      | FStar_Parser_AST.NoName t ->
          let uu____71238 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71238)
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
      fun uu___441_71246  ->
        match uu___441_71246 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____71268 = FStar_Syntax_Syntax.null_binder k  in
            (uu____71268, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71285 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71285 with
             | (env1,a1) ->
                 let uu____71302 =
                   let uu____71309 = trans_aqual env1 imp  in
                   ((let uu___2962_71315 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_71315.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_71315.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____71309)
                    in
                 (uu____71302, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_71323  ->
      match uu___442_71323 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____71327 =
            let uu____71328 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____71328  in
          FStar_Pervasives_Native.Some uu____71327
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____71344) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____71346) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____71349 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____71367 = binder_ident b  in
         FStar_Common.list_of_option uu____71367) bs
  
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
               (fun uu___443_71404  ->
                  match uu___443_71404 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____71409 -> false))
           in
        let quals2 q =
          let uu____71423 =
            (let uu____71427 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____71427) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____71423
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____71444 = FStar_Ident.range_of_lid disc_name  in
                let uu____71445 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____71444;
                  FStar_Syntax_Syntax.sigquals = uu____71445;
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
            let uu____71485 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____71523  ->
                        match uu____71523 with
                        | (x,uu____71534) ->
                            let uu____71539 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____71539 with
                             | (field_name,uu____71547) ->
                                 let only_decl =
                                   ((let uu____71552 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____71552)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____71554 =
                                        let uu____71556 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____71556.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____71554)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____71574 =
                                       FStar_List.filter
                                         (fun uu___444_71578  ->
                                            match uu___444_71578 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____71581 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____71574
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_71596  ->
                                             match uu___445_71596 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____71601 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____71604 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____71604;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____71611 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____71611
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____71622 =
                                        let uu____71627 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____71627  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____71622;
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
                                      let uu____71631 =
                                        let uu____71632 =
                                          let uu____71639 =
                                            let uu____71642 =
                                              let uu____71643 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____71643
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____71642]  in
                                          ((false, [lb]), uu____71639)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____71632
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____71631;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____71485 FStar_List.flatten
  
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
            (lid,uu____71692,t,uu____71694,n1,uu____71696) when
            let uu____71703 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____71703 ->
            let uu____71705 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____71705 with
             | (formals,uu____71723) ->
                 (match formals with
                  | [] -> []
                  | uu____71752 ->
                      let filter_records uu___446_71768 =
                        match uu___446_71768 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____71771,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____71783 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____71785 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____71785 with
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
                      let uu____71797 = FStar_Util.first_N n1 formals  in
                      (match uu____71797 with
                       | (uu____71826,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____71860 -> []
  
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
                    let uu____71939 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____71939
                    then
                      let uu____71945 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____71945
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____71949 =
                      let uu____71954 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____71954  in
                    let uu____71955 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____71961 =
                          let uu____71964 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____71964  in
                        FStar_Syntax_Util.arrow typars uu____71961
                      else FStar_Syntax_Syntax.tun  in
                    let uu____71969 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____71949;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____71955;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____71969;
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
          let tycon_id uu___447_72023 =
            match uu___447_72023 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72025,uu____72026) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72036,uu____72037,uu____72038) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72048,uu____72049,uu____72050) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72080,uu____72081,uu____72082) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72128) ->
                let uu____72129 =
                  let uu____72130 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72130  in
                FStar_Parser_AST.mk_term uu____72129 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72132 =
                  let uu____72133 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72133  in
                FStar_Parser_AST.mk_term uu____72132 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72135) ->
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
              | uu____72166 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72174 =
                     let uu____72175 =
                       let uu____72182 = binder_to_term b  in
                       (out, uu____72182, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72175  in
                   FStar_Parser_AST.mk_term uu____72174
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72194 =
            match uu___448_72194 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72251  ->
                       match uu____72251 with
                       | (x,t,uu____72262) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____72268 =
                    let uu____72269 =
                      let uu____72270 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____72270  in
                    FStar_Parser_AST.mk_term uu____72269
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____72268 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____72277 = binder_idents parms  in id1 ::
                    uu____72277
                   in
                (FStar_List.iter
                   (fun uu____72295  ->
                      match uu____72295 with
                      | (f,uu____72305,uu____72306) ->
                          let uu____72311 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____72311
                          then
                            let uu____72316 =
                              let uu____72322 =
                                let uu____72324 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____72324
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____72322)
                               in
                            FStar_Errors.raise_error uu____72316
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____72330 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____72357  ->
                            match uu____72357 with
                            | (x,uu____72367,uu____72368) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____72330)))
            | uu____72426 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_72466 =
            match uu___449_72466 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____72490 = typars_of_binders _env binders  in
                (match uu____72490 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____72526 =
                         let uu____72527 =
                           let uu____72528 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____72528  in
                         FStar_Parser_AST.mk_term uu____72527
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____72526 binders  in
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
            | uu____72539 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____72582 =
              FStar_List.fold_left
                (fun uu____72616  ->
                   fun uu____72617  ->
                     match (uu____72616, uu____72617) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____72686 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____72686 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____72582 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____72777 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____72777
                | uu____72778 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____72786 = desugar_abstract_tc quals env [] tc  in
              (match uu____72786 with
               | (uu____72799,uu____72800,se,uu____72802) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____72805,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____72824 =
                                 let uu____72826 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____72826  in
                               if uu____72824
                               then
                                 let uu____72829 =
                                   let uu____72835 =
                                     let uu____72837 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____72837
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____72835)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____72829
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
                           | uu____72850 ->
                               let uu____72851 =
                                 let uu____72858 =
                                   let uu____72859 =
                                     let uu____72874 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____72874)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____72859
                                    in
                                 FStar_Syntax_Syntax.mk uu____72858  in
                               uu____72851 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_72887 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_72887.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_72887.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_72887.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____72888 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____72892 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____72892
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____72905 = typars_of_binders env binders  in
              (match uu____72905 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____72939 =
                           FStar_Util.for_some
                             (fun uu___450_72942  ->
                                match uu___450_72942 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____72945 -> false) quals
                            in
                         if uu____72939
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____72953 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____72953
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____72958 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_72964  ->
                               match uu___451_72964 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____72967 -> false))
                        in
                     if uu____72958
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____72981 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____72981
                     then
                       let uu____72987 =
                         let uu____72994 =
                           let uu____72995 = unparen t  in
                           uu____72995.FStar_Parser_AST.tm  in
                         match uu____72994 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73016 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73046)::args_rev ->
                                   let uu____73058 =
                                     let uu____73059 = unparen last_arg  in
                                     uu____73059.FStar_Parser_AST.tm  in
                                   (match uu____73058 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73087 -> ([], args))
                               | uu____73096 -> ([], args)  in
                             (match uu____73016 with
                              | (cattributes,args1) ->
                                  let uu____73135 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73135))
                         | uu____73146 -> (t, [])  in
                       match uu____72987 with
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
                                  (fun uu___452_73169  ->
                                     match uu___452_73169 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73172 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73181)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73205 = tycon_record_as_variant trec  in
              (match uu____73205 with
               | (t,fs) ->
                   let uu____73222 =
                     let uu____73225 =
                       let uu____73226 =
                         let uu____73235 =
                           let uu____73238 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73238  in
                         (uu____73235, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73226  in
                     uu____73225 :: quals  in
                   desugar_tycon env d uu____73222 [t])
          | uu____73243::uu____73244 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____73414 = et  in
                match uu____73414 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____73644 ->
                         let trec = tc  in
                         let uu____73668 = tycon_record_as_variant trec  in
                         (match uu____73668 with
                          | (t,fs) ->
                              let uu____73728 =
                                let uu____73731 =
                                  let uu____73732 =
                                    let uu____73741 =
                                      let uu____73744 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____73744  in
                                    (uu____73741, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____73732
                                   in
                                uu____73731 :: quals1  in
                              collect_tcs uu____73728 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____73834 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____73834 with
                          | (env2,uu____73895,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74048 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74048 with
                          | (env2,uu____74109,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74237 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____74287 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____74287 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_74802  ->
                             match uu___454_74802 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____74868,uu____74869);
                                    FStar_Syntax_Syntax.sigrng = uu____74870;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____74871;
                                    FStar_Syntax_Syntax.sigmeta = uu____74872;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____74873;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____74937 =
                                     typars_of_binders env1 binders  in
                                   match uu____74937 with
                                   | (env2,tpars1) ->
                                       let uu____74964 =
                                         push_tparams env2 tpars1  in
                                       (match uu____74964 with
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
                                 let uu____74993 =
                                   let uu____75012 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75012)
                                    in
                                 [uu____74993]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75072);
                                    FStar_Syntax_Syntax.sigrng = uu____75073;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75075;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75076;_},constrs,tconstr,quals1)
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
                                 let uu____75177 = push_tparams env1 tpars
                                    in
                                 (match uu____75177 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75244  ->
                                             match uu____75244 with
                                             | (x,uu____75256) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75261 =
                                        let uu____75288 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____75398  ->
                                                  match uu____75398 with
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
                                                        let uu____75458 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____75458
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
                                                                uu___453_75469
                                                                 ->
                                                                match uu___453_75469
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____75481
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____75489 =
                                                        let uu____75508 =
                                                          let uu____75509 =
                                                            let uu____75510 =
                                                              let uu____75526
                                                                =
                                                                let uu____75527
                                                                  =
                                                                  let uu____75530
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____75530
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____75527
                                                                 in
                                                              (name, univs1,
                                                                uu____75526,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____75510
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____75509;
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
                                                          uu____75508)
                                                         in
                                                      (name, uu____75489)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____75288
                                         in
                                      (match uu____75261 with
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
                             | uu____75742 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75870  ->
                             match uu____75870 with
                             | (name_doc,uu____75896,uu____75897) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75969  ->
                             match uu____75969 with
                             | (uu____75988,uu____75989,se) -> se))
                      in
                   let uu____76015 =
                     let uu____76022 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76022 rng
                      in
                   (match uu____76015 with
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
                               (fun uu____76084  ->
                                  match uu____76084 with
                                  | (uu____76105,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76153,tps,k,uu____76156,constrs)
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
                                      let uu____76177 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76192 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76209,uu____76210,uu____76211,uu____76212,uu____76213)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76220
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76192
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76224 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76231 
                                                          ->
                                                          match uu___455_76231
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76233 ->
                                                              true
                                                          | uu____76243 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76224))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76177
                                  | uu____76245 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76262  ->
                                 match uu____76262 with
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
      let uu____76307 =
        FStar_List.fold_left
          (fun uu____76342  ->
             fun b  ->
               match uu____76342 with
               | (env1,binders1) ->
                   let uu____76386 = desugar_binder env1 b  in
                   (match uu____76386 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____76409 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____76409 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____76462 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____76307 with
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
          let uu____76566 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_76573  ->
                    match uu___456_76573 with
                    | FStar_Syntax_Syntax.Reflectable uu____76575 -> true
                    | uu____76577 -> false))
             in
          if uu____76566
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____76582 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____76582
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
      let uu____76623 = FStar_Syntax_Util.head_and_args at1  in
      match uu____76623 with
      | (hd1,args) ->
          let uu____76676 =
            let uu____76691 =
              let uu____76692 = FStar_Syntax_Subst.compress hd1  in
              uu____76692.FStar_Syntax_Syntax.n  in
            (uu____76691, args)  in
          (match uu____76676 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____76717)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____76752 =
                 let uu____76757 =
                   let uu____76766 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____76766 a1  in
                 uu____76757 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____76752 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____76792 =
                      let uu____76801 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____76801, b)  in
                    FStar_Pervasives_Native.Some uu____76792
                | uu____76818 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____76872) when
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
           | uu____76907 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77079 = desugar_binders monad_env eff_binders  in
                  match uu____77079 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77119 =
                          let uu____77121 =
                            let uu____77130 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77130  in
                          FStar_List.length uu____77121  in
                        uu____77119 = (Prims.parse_int "1")  in
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
                            (uu____77214,uu____77215,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77217,uu____77218,uu____77219),uu____77220)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77257 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77260 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____77272 = name_of_eff_decl decl  in
                             FStar_List.mem uu____77272 mandatory_members)
                          eff_decls
                         in
                      (match uu____77260 with
                       | (mandatory_members_decls,actions) ->
                           let uu____77291 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____77320  ->
                                     fun decl  ->
                                       match uu____77320 with
                                       | (env2,out) ->
                                           let uu____77340 =
                                             desugar_decl env2 decl  in
                                           (match uu____77340 with
                                            | (env3,ses) ->
                                                let uu____77353 =
                                                  let uu____77356 =
                                                    FStar_List.hd ses  in
                                                  uu____77356 :: out  in
                                                (env3, uu____77353)))
                                  (env1, []))
                              in
                           (match uu____77291 with
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
                                              (uu____77425,uu____77426,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77429,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____77430,(def,uu____77432)::
                                                      (cps_type,uu____77434)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____77435;
                                                   FStar_Parser_AST.level =
                                                     uu____77436;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____77492 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77492 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77530 =
                                                     let uu____77531 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77532 =
                                                       let uu____77533 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77533
                                                        in
                                                     let uu____77540 =
                                                       let uu____77541 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77541
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77531;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77532;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____77540
                                                     }  in
                                                   (uu____77530, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____77550,uu____77551,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77554,defn),doc1)::[])
                                              when for_free ->
                                              let uu____77593 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77593 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77631 =
                                                     let uu____77632 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77633 =
                                                       let uu____77634 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77634
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77632;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77633;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____77631, doc1))
                                          | uu____77643 ->
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
                                    let uu____77679 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____77679
                                     in
                                  let uu____77681 =
                                    let uu____77682 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____77682
                                     in
                                  ([], uu____77681)  in
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
                                      let uu____77700 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____77700)  in
                                    let uu____77707 =
                                      let uu____77708 =
                                        let uu____77709 =
                                          let uu____77710 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____77710
                                           in
                                        let uu____77720 = lookup1 "return"
                                           in
                                        let uu____77722 = lookup1 "bind"  in
                                        let uu____77724 =
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
                                            uu____77709;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____77720;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____77722;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____77724
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____77708
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____77707;
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
                                         (fun uu___457_77732  ->
                                            match uu___457_77732 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____77735 -> true
                                            | uu____77737 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____77752 =
                                       let uu____77753 =
                                         let uu____77754 =
                                           lookup1 "return_wp"  in
                                         let uu____77756 = lookup1 "bind_wp"
                                            in
                                         let uu____77758 =
                                           lookup1 "if_then_else"  in
                                         let uu____77760 = lookup1 "ite_wp"
                                            in
                                         let uu____77762 = lookup1 "stronger"
                                            in
                                         let uu____77764 = lookup1 "close_wp"
                                            in
                                         let uu____77766 = lookup1 "assert_p"
                                            in
                                         let uu____77768 = lookup1 "assume_p"
                                            in
                                         let uu____77770 = lookup1 "null_wp"
                                            in
                                         let uu____77772 = lookup1 "trivial"
                                            in
                                         let uu____77774 =
                                           if rr
                                           then
                                             let uu____77776 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____77776
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____77794 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____77799 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____77804 =
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
                                             uu____77754;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____77756;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____77758;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____77760;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____77762;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____77764;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____77766;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____77768;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____77770;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____77772;
                                           FStar_Syntax_Syntax.repr =
                                             uu____77774;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____77794;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____77799;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____77804
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____77753
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____77752;
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
                                          fun uu____77830  ->
                                            match uu____77830 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____77844 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____77844
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
                let uu____77868 = desugar_binders env1 eff_binders  in
                match uu____77868 with
                | (env2,binders) ->
                    let uu____77905 =
                      let uu____77916 = head_and_args defn  in
                      match uu____77916 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____77953 ->
                                let uu____77954 =
                                  let uu____77960 =
                                    let uu____77962 =
                                      let uu____77964 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____77964 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____77962  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____77960)
                                   in
                                FStar_Errors.raise_error uu____77954
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____77970 =
                            match FStar_List.rev args with
                            | (last_arg,uu____78000)::args_rev ->
                                let uu____78012 =
                                  let uu____78013 = unparen last_arg  in
                                  uu____78013.FStar_Parser_AST.tm  in
                                (match uu____78012 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78041 -> ([], args))
                            | uu____78050 -> ([], args)  in
                          (match uu____77970 with
                           | (cattributes,args1) ->
                               let uu____78093 = desugar_args env2 args1  in
                               let uu____78094 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78093, uu____78094))
                       in
                    (match uu____77905 with
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
                          (let uu____78134 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78134 with
                           | (ed_binders,uu____78148,ed_binders_opening) ->
                               let sub' shift_n uu____78167 =
                                 match uu____78167 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78182 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78182 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78186 =
                                       let uu____78187 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78187)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78186
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78208 =
                                   let uu____78209 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78209
                                    in
                                 let uu____78224 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78225 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78226 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78227 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78228 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78229 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78230 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78231 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78232 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78233 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78234 =
                                   let uu____78235 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78235
                                    in
                                 let uu____78250 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78251 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78252 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____78268 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____78269 =
                                          let uu____78270 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78270
                                           in
                                        let uu____78285 =
                                          let uu____78286 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78286
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____78268;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____78269;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____78285
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
                                     uu____78208;
                                   FStar_Syntax_Syntax.ret_wp = uu____78224;
                                   FStar_Syntax_Syntax.bind_wp = uu____78225;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78226;
                                   FStar_Syntax_Syntax.ite_wp = uu____78227;
                                   FStar_Syntax_Syntax.stronger = uu____78228;
                                   FStar_Syntax_Syntax.close_wp = uu____78229;
                                   FStar_Syntax_Syntax.assert_p = uu____78230;
                                   FStar_Syntax_Syntax.assume_p = uu____78231;
                                   FStar_Syntax_Syntax.null_wp = uu____78232;
                                   FStar_Syntax_Syntax.trivial = uu____78233;
                                   FStar_Syntax_Syntax.repr = uu____78234;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78250;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78251;
                                   FStar_Syntax_Syntax.actions = uu____78252;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____78304 =
                                     let uu____78306 =
                                       let uu____78315 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____78315
                                        in
                                     FStar_List.length uu____78306  in
                                   uu____78304 = (Prims.parse_int "1")  in
                                 let uu____78348 =
                                   let uu____78351 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____78351 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____78348;
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
                                             let uu____78375 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____78375
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____78377 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____78377
                                 then
                                   let reflect_lid =
                                     let uu____78384 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____78384
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
    let uu____78396 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____78396 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____78481 ->
              let uu____78484 =
                let uu____78486 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____78486
                 in
              Prims.op_Hat "\n  " uu____78484
          | uu____78489 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____78508  ->
               match uu____78508 with
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
          let uu____78553 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____78553
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____78556 =
          let uu____78567 = FStar_Syntax_Syntax.as_arg arg  in [uu____78567]
           in
        FStar_Syntax_Util.mk_app fv uu____78556

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78598 = desugar_decl_noattrs env d  in
      match uu____78598 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____78616 = mk_comment_attr d  in uu____78616 :: attrs1  in
          let uu____78617 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_78627 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_78627.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_78627.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_78627.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_78627.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_78630 = sigelt  in
                      let uu____78631 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____78637 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____78637) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_78630.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_78630.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_78630.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_78630.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____78631
                      })) sigelts
             in
          (env1, uu____78617)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78663 = desugar_decl_aux env d  in
      match uu____78663 with
      | (env1,ses) ->
          let uu____78674 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____78674)

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
      | FStar_Parser_AST.Fsdoc uu____78702 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____78707 = FStar_Syntax_DsEnv.iface env  in
          if uu____78707
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____78722 =
               let uu____78724 =
                 let uu____78726 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____78727 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____78726
                   uu____78727
                  in
               Prims.op_Negation uu____78724  in
             if uu____78722
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____78741 =
                  let uu____78743 =
                    let uu____78745 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____78745 lid  in
                  Prims.op_Negation uu____78743  in
                if uu____78741
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____78759 =
                     let uu____78761 =
                       let uu____78763 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____78763
                         lid
                        in
                     Prims.op_Negation uu____78761  in
                   if uu____78759
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____78781 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____78781, [])
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
              | (FStar_Parser_AST.TyconRecord uu____78822,uu____78823)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____78862 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____78889  ->
                 match uu____78889 with | (x,uu____78897) -> x) tcs
             in
          let uu____78902 =
            let uu____78907 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____78907 tcs1  in
          (match uu____78902 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____78924 =
                   let uu____78925 =
                     let uu____78932 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____78932  in
                   [uu____78925]  in
                 let uu____78945 =
                   let uu____78948 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____78951 =
                     let uu____78962 =
                       let uu____78971 =
                         let uu____78972 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____78972  in
                       FStar_Syntax_Syntax.as_arg uu____78971  in
                     [uu____78962]  in
                   FStar_Syntax_Util.mk_app uu____78948 uu____78951  in
                 FStar_Syntax_Util.abs uu____78924 uu____78945
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79012,id1))::uu____79014 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79017::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79021 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79021 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79027 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79027]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79048) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79058,uu____79059,uu____79060,uu____79061,uu____79062)
                     ->
                     let uu____79071 =
                       let uu____79072 =
                         let uu____79073 =
                           let uu____79080 = mkclass lid  in
                           (meths, uu____79080)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79073  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79072;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79071]
                 | uu____79083 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79117;
                    FStar_Parser_AST.prange = uu____79118;_},uu____79119)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79129;
                    FStar_Parser_AST.prange = uu____79130;_},uu____79131)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79147;
                         FStar_Parser_AST.prange = uu____79148;_},uu____79149);
                    FStar_Parser_AST.prange = uu____79150;_},uu____79151)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79173;
                         FStar_Parser_AST.prange = uu____79174;_},uu____79175);
                    FStar_Parser_AST.prange = uu____79176;_},uu____79177)::[]
                   -> false
               | (p,uu____79206)::[] ->
                   let uu____79215 = is_app_pattern p  in
                   Prims.op_Negation uu____79215
               | uu____79217 -> false)
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
            let uu____79292 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____79292 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____79305 =
                     let uu____79306 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____79306.FStar_Syntax_Syntax.n  in
                   match uu____79305 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____79316) ->
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
                         | uu____79352::uu____79353 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____79356 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_79372  ->
                                     match uu___458_79372 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____79375;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79376;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79377;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79378;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79379;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79380;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79381;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79393;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79394;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79395;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79396;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79397;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79398;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____79412 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____79445  ->
                                   match uu____79445 with
                                   | (uu____79459,(uu____79460,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____79412
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____79480 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____79480
                         then
                           let uu____79486 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_79501 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_79503 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_79503.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_79503.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_79501.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____79486)
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
                   | uu____79533 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____79541 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____79560 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____79541 with
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
                       let uu___4019_79597 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_79597.FStar_Parser_AST.prange)
                       }
                   | uu____79604 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_79611 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_79611.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_79611.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_79611.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____79647 id1 =
                   match uu____79647 with
                   | (env1,ses) ->
                       let main =
                         let uu____79668 =
                           let uu____79669 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____79669  in
                         FStar_Parser_AST.mk_term uu____79668
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
                       let uu____79719 = desugar_decl env1 id_decl  in
                       (match uu____79719 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____79737 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____79737 FStar_Util.set_elements
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
            let uu____79761 = close_fun env t  in
            desugar_term env uu____79761  in
          let quals1 =
            let uu____79765 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____79765
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____79777 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____79777;
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
                let uu____79791 =
                  let uu____79800 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____79800]  in
                let uu____79819 =
                  let uu____79822 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____79822
                   in
                FStar_Syntax_Util.arrow uu____79791 uu____79819
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
            let uu____79877 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____79877 with
            | FStar_Pervasives_Native.None  ->
                let uu____79880 =
                  let uu____79886 =
                    let uu____79888 =
                      let uu____79890 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____79890 " not found"  in
                    Prims.op_Hat "Effect name " uu____79888  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____79886)  in
                FStar_Errors.raise_error uu____79880
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____79898 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____79916 =
                  let uu____79919 =
                    let uu____79920 = desugar_term env t  in
                    ([], uu____79920)  in
                  FStar_Pervasives_Native.Some uu____79919  in
                (uu____79916, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____79933 =
                  let uu____79936 =
                    let uu____79937 = desugar_term env wp  in
                    ([], uu____79937)  in
                  FStar_Pervasives_Native.Some uu____79936  in
                let uu____79944 =
                  let uu____79947 =
                    let uu____79948 = desugar_term env t  in
                    ([], uu____79948)  in
                  FStar_Pervasives_Native.Some uu____79947  in
                (uu____79933, uu____79944)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____79960 =
                  let uu____79963 =
                    let uu____79964 = desugar_term env t  in
                    ([], uu____79964)  in
                  FStar_Pervasives_Native.Some uu____79963  in
                (FStar_Pervasives_Native.None, uu____79960)
             in
          (match uu____79898 with
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
            let uu____79998 =
              let uu____79999 =
                let uu____80006 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80006, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____79999  in
            {
              FStar_Syntax_Syntax.sigel = uu____79998;
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
      let uu____80033 =
        FStar_List.fold_left
          (fun uu____80053  ->
             fun d  ->
               match uu____80053 with
               | (env1,sigelts) ->
                   let uu____80073 = desugar_decl env1 d  in
                   (match uu____80073 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80033 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80118 =
            match uu___460_80118 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80132,FStar_Syntax_Syntax.Sig_let uu____80133) ->
                     let uu____80146 =
                       let uu____80149 =
                         let uu___4152_80150 = se2  in
                         let uu____80151 =
                           let uu____80154 =
                             FStar_List.filter
                               (fun uu___459_80168  ->
                                  match uu___459_80168 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80173;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80174;_},uu____80175);
                                      FStar_Syntax_Syntax.pos = uu____80176;
                                      FStar_Syntax_Syntax.vars = uu____80177;_}
                                      when
                                      let uu____80204 =
                                        let uu____80206 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80206
                                         in
                                      uu____80204 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80210 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80154
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80150.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80150.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80150.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80150.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80151
                         }  in
                       uu____80149 :: se1 :: acc  in
                     forward uu____80146 sigelts1
                 | uu____80216 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80224 = forward [] sigelts  in (env1, uu____80224)
  
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
          | (FStar_Pervasives_Native.None ,uu____80289) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____80293;
               FStar_Syntax_Syntax.exports = uu____80294;
               FStar_Syntax_Syntax.is_interface = uu____80295;_},FStar_Parser_AST.Module
             (current_lid,uu____80297)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____80306) ->
              let uu____80309 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____80309
           in
        let uu____80314 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____80356 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80356, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____80378 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80378, mname, decls, false)
           in
        match uu____80314 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____80420 = desugar_decls env2 decls  in
            (match uu____80420 with
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
          let uu____80488 =
            (FStar_Options.interactive ()) &&
              (let uu____80491 =
                 let uu____80493 =
                   let uu____80495 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____80495  in
                 FStar_Util.get_file_extension uu____80493  in
               FStar_List.mem uu____80491 ["fsti"; "fsi"])
             in
          if uu____80488 then as_interface m else m  in
        let uu____80509 = desugar_modul_common curmod env m1  in
        match uu____80509 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____80531 = FStar_Syntax_DsEnv.pop ()  in
              (uu____80531, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____80553 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____80553 with
      | (env1,modul,pop_when_done) ->
          let uu____80570 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____80570 with
           | (env2,modul1) ->
               ((let uu____80582 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____80582
                 then
                   let uu____80585 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____80585
                 else ());
                (let uu____80590 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____80590, modul1))))
  
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
        (fun uu____80640  ->
           let uu____80641 = desugar_modul env modul  in
           match uu____80641 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____80679  ->
           let uu____80680 = desugar_decls env decls  in
           match uu____80680 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____80731  ->
             let uu____80732 = desugar_partial_modul modul env a_modul  in
             match uu____80732 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____80827 ->
                  let t =
                    let uu____80837 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____80837  in
                  let uu____80850 =
                    let uu____80851 = FStar_Syntax_Subst.compress t  in
                    uu____80851.FStar_Syntax_Syntax.n  in
                  (match uu____80850 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____80863,uu____80864)
                       -> bs1
                   | uu____80889 -> failwith "Impossible")
               in
            let uu____80899 =
              let uu____80906 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____80906
                FStar_Syntax_Syntax.t_unit
               in
            match uu____80899 with
            | (binders,uu____80908,binders_opening) ->
                let erase_term t =
                  let uu____80916 =
                    let uu____80917 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____80917  in
                  FStar_Syntax_Subst.close binders uu____80916  in
                let erase_tscheme uu____80935 =
                  match uu____80935 with
                  | (us,t) ->
                      let t1 =
                        let uu____80955 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____80955 t  in
                      let uu____80958 =
                        let uu____80959 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____80959  in
                      ([], uu____80958)
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
                    | uu____80982 ->
                        let bs =
                          let uu____80992 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____80992  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81032 =
                          let uu____81033 =
                            let uu____81036 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81036  in
                          uu____81033.FStar_Syntax_Syntax.n  in
                        (match uu____81032 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81038,uu____81039) -> bs1
                         | uu____81064 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81072 =
                      let uu____81073 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81073  in
                    FStar_Syntax_Subst.close binders uu____81072  in
                  let uu___4311_81074 = action  in
                  let uu____81075 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81076 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81074.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81074.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81075;
                    FStar_Syntax_Syntax.action_typ = uu____81076
                  }  in
                let uu___4313_81077 = ed  in
                let uu____81078 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81079 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81080 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81081 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81082 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81083 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81084 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81085 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81086 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81087 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81088 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81089 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81090 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81091 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81092 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81093 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81077.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81077.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81078;
                  FStar_Syntax_Syntax.signature = uu____81079;
                  FStar_Syntax_Syntax.ret_wp = uu____81080;
                  FStar_Syntax_Syntax.bind_wp = uu____81081;
                  FStar_Syntax_Syntax.if_then_else = uu____81082;
                  FStar_Syntax_Syntax.ite_wp = uu____81083;
                  FStar_Syntax_Syntax.stronger = uu____81084;
                  FStar_Syntax_Syntax.close_wp = uu____81085;
                  FStar_Syntax_Syntax.assert_p = uu____81086;
                  FStar_Syntax_Syntax.assume_p = uu____81087;
                  FStar_Syntax_Syntax.null_wp = uu____81088;
                  FStar_Syntax_Syntax.trivial = uu____81089;
                  FStar_Syntax_Syntax.repr = uu____81090;
                  FStar_Syntax_Syntax.return_repr = uu____81091;
                  FStar_Syntax_Syntax.bind_repr = uu____81092;
                  FStar_Syntax_Syntax.actions = uu____81093;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81077.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81109 = se  in
                  let uu____81110 =
                    let uu____81111 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81111  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81110;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81109.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81109.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81109.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81109.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81115 = se  in
                  let uu____81116 =
                    let uu____81117 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81117
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81116;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81115.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81115.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81115.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81115.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81119 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81120 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81120 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81137 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81137
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81139 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81139)
  