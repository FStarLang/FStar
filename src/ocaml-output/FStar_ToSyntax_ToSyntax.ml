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
             (fun uu____53506  ->
                match uu____53506 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____53561  ->
                             match uu____53561 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____53579 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____53579 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____53585 =
                                     let uu____53586 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____53586]  in
                                   FStar_Syntax_Subst.close uu____53585
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
      fun uu___429_53643  ->
        match uu___429_53643 with
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
  fun uu___430_53663  ->
    match uu___430_53663 with
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
  fun uu___431_53681  ->
    match uu___431_53681 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____53684 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____53692 .
    FStar_Parser_AST.imp ->
      'Auu____53692 ->
        ('Auu____53692 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____53718 .
    FStar_Parser_AST.imp ->
      'Auu____53718 ->
        ('Auu____53718 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53737 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53758 -> true
            | uu____53764 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53773 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53780 =
      let uu____53781 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53781  in
    FStar_Parser_AST.mk_term uu____53780 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53791 =
      let uu____53792 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53792  in
    FStar_Parser_AST.mk_term uu____53791 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53808 =
        let uu____53809 = unparen t  in uu____53809.FStar_Parser_AST.tm  in
      match uu____53808 with
      | FStar_Parser_AST.Name l ->
          let uu____53812 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53812 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53819) ->
          let uu____53832 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53832 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53839,uu____53840) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53845,uu____53846) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53851,t1) -> is_comp_type env t1
      | uu____53853 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53954;
                            FStar_Syntax_Syntax.vars = uu____53955;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53983 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53983 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53999 =
                               let uu____54000 =
                                 let uu____54003 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____54003  in
                               uu____54000.FStar_Syntax_Syntax.n  in
                             match uu____53999 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____54026))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____54033 -> msg
                           else msg  in
                         let uu____54036 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____54036
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____54041 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____54041 " is deprecated"  in
                         let uu____54044 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____54044
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____54046 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____54062 .
    'Auu____54062 ->
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
        let uu____54115 =
          let uu____54118 =
            let uu____54119 =
              let uu____54125 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____54125, r)  in
            FStar_Ident.mk_ident uu____54119  in
          [uu____54118]  in
        FStar_All.pipe_right uu____54115 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____54141 .
    env_t ->
      Prims.int ->
        'Auu____54141 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____54179 =
              let uu____54180 =
                let uu____54181 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____54181 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____54180 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____54179  in
          let fallback uu____54189 =
            let uu____54190 = FStar_Ident.text_of_id op  in
            match uu____54190 with
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
                let uu____54211 = FStar_Options.ml_ish ()  in
                if uu____54211
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
            | uu____54236 -> FStar_Pervasives_Native.None  in
          let uu____54238 =
            let uu____54241 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_54247 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_54247.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_54247.FStar_Syntax_Syntax.vars)
                 }) env true uu____54241
             in
          match uu____54238 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____54252 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____54267 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____54267
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____54316 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____54320 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____54320 with | (env1,uu____54332) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____54335,term) ->
          let uu____54337 = free_type_vars env term  in (env, uu____54337)
      | FStar_Parser_AST.TAnnotated (id1,uu____54343) ->
          let uu____54344 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____54344 with | (env1,uu____54356) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____54360 = free_type_vars env t  in (env, uu____54360)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____54367 =
        let uu____54368 = unparen t  in uu____54368.FStar_Parser_AST.tm  in
      match uu____54367 with
      | FStar_Parser_AST.Labeled uu____54371 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____54384 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____54384 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____54389 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____54392 -> []
      | FStar_Parser_AST.Uvar uu____54393 -> []
      | FStar_Parser_AST.Var uu____54394 -> []
      | FStar_Parser_AST.Projector uu____54395 -> []
      | FStar_Parser_AST.Discrim uu____54400 -> []
      | FStar_Parser_AST.Name uu____54401 -> []
      | FStar_Parser_AST.Requires (t1,uu____54403) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____54411) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____54418,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____54437,ts) ->
          FStar_List.collect
            (fun uu____54458  ->
               match uu____54458 with
               | (t1,uu____54466) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____54467,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____54475) ->
          let uu____54476 = free_type_vars env t1  in
          let uu____54479 = free_type_vars env t2  in
          FStar_List.append uu____54476 uu____54479
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____54484 = free_type_vars_b env b  in
          (match uu____54484 with
           | (env1,f) ->
               let uu____54499 = free_type_vars env1 t1  in
               FStar_List.append f uu____54499)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____54516 =
            FStar_List.fold_left
              (fun uu____54540  ->
                 fun bt  ->
                   match uu____54540 with
                   | (env1,free) ->
                       let uu____54564 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____54579 = free_type_vars env1 body  in
                             (env1, uu____54579)
                          in
                       (match uu____54564 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____54516 with
           | (env1,free) ->
               let uu____54608 = free_type_vars env1 body  in
               FStar_List.append free uu____54608)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____54617 =
            FStar_List.fold_left
              (fun uu____54637  ->
                 fun binder  ->
                   match uu____54637 with
                   | (env1,free) ->
                       let uu____54657 = free_type_vars_b env1 binder  in
                       (match uu____54657 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____54617 with
           | (env1,free) ->
               let uu____54688 = free_type_vars env1 body  in
               FStar_List.append free uu____54688)
      | FStar_Parser_AST.Project (t1,uu____54692) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____54703 = free_type_vars env rel  in
          let uu____54706 =
            let uu____54709 = free_type_vars env init1  in
            let uu____54712 =
              FStar_List.collect
                (fun uu____54721  ->
                   match uu____54721 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____54727 = free_type_vars env rel1  in
                       let uu____54730 =
                         let uu____54733 = free_type_vars env just  in
                         let uu____54736 = free_type_vars env next  in
                         FStar_List.append uu____54733 uu____54736  in
                       FStar_List.append uu____54727 uu____54730) steps
               in
            FStar_List.append uu____54709 uu____54712  in
          FStar_List.append uu____54703 uu____54706
      | FStar_Parser_AST.Abs uu____54739 -> []
      | FStar_Parser_AST.Let uu____54746 -> []
      | FStar_Parser_AST.LetOpen uu____54767 -> []
      | FStar_Parser_AST.If uu____54772 -> []
      | FStar_Parser_AST.QForall uu____54779 -> []
      | FStar_Parser_AST.QExists uu____54792 -> []
      | FStar_Parser_AST.Record uu____54805 -> []
      | FStar_Parser_AST.Match uu____54818 -> []
      | FStar_Parser_AST.TryWith uu____54833 -> []
      | FStar_Parser_AST.Bind uu____54848 -> []
      | FStar_Parser_AST.Quote uu____54855 -> []
      | FStar_Parser_AST.VQuote uu____54860 -> []
      | FStar_Parser_AST.Antiquote uu____54861 -> []
      | FStar_Parser_AST.Seq uu____54862 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54916 =
        let uu____54917 = unparen t1  in uu____54917.FStar_Parser_AST.tm  in
      match uu____54916 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54959 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54984 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54984  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____55006 =
                     let uu____55007 =
                       let uu____55012 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____55012)  in
                     FStar_Parser_AST.TAnnotated uu____55007  in
                   FStar_Parser_AST.mk_binder uu____55006
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
        let uu____55030 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____55030  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____55052 =
                     let uu____55053 =
                       let uu____55058 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____55058)  in
                     FStar_Parser_AST.TAnnotated uu____55053  in
                   FStar_Parser_AST.mk_binder uu____55052
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____55060 =
             let uu____55061 = unparen t  in uu____55061.FStar_Parser_AST.tm
              in
           match uu____55060 with
           | FStar_Parser_AST.Product uu____55062 -> t
           | uu____55069 ->
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
      | uu____55106 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____55117 -> true
    | FStar_Parser_AST.PatTvar (uu____55121,uu____55122) -> true
    | FStar_Parser_AST.PatVar (uu____55128,uu____55129) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____55136) -> is_var_pattern p1
    | uu____55149 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____55160) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____55173;
           FStar_Parser_AST.prange = uu____55174;_},uu____55175)
        -> true
    | uu____55187 -> false
  
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
    | uu____55203 -> p
  
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
            let uu____55276 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____55276 with
             | (name,args,uu____55319) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____55369);
               FStar_Parser_AST.prange = uu____55370;_},args)
            when is_top_level1 ->
            let uu____55380 =
              let uu____55385 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____55385  in
            (uu____55380, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____55407);
               FStar_Parser_AST.prange = uu____55408;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____55438 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____55497 -> acc
        | FStar_Parser_AST.PatName uu____55500 -> acc
        | FStar_Parser_AST.PatOp uu____55501 -> acc
        | FStar_Parser_AST.PatConst uu____55502 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____55519) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____55525) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____55534) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____55551 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____55551
        | FStar_Parser_AST.PatAscribed (pat,uu____55559) ->
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
    match projectee with | LocalBinder _0 -> true | uu____55641 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____55683 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_55732  ->
    match uu___432_55732 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55739 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55772  ->
    match uu____55772 with
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
      let uu____55854 =
        let uu____55871 =
          let uu____55874 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55874  in
        let uu____55875 =
          let uu____55886 =
            let uu____55895 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55895)  in
          [uu____55886]  in
        (uu____55871, uu____55875)  in
      FStar_Syntax_Syntax.Tm_app uu____55854  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55944 =
        let uu____55961 =
          let uu____55964 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55964  in
        let uu____55965 =
          let uu____55976 =
            let uu____55985 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55985)  in
          [uu____55976]  in
        (uu____55961, uu____55965)  in
      FStar_Syntax_Syntax.Tm_app uu____55944  in
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
          let uu____56048 =
            let uu____56065 =
              let uu____56068 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____56068  in
            let uu____56069 =
              let uu____56080 =
                let uu____56089 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____56089)  in
              let uu____56097 =
                let uu____56108 =
                  let uu____56117 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____56117)  in
                [uu____56108]  in
              uu____56080 :: uu____56097  in
            (uu____56065, uu____56069)  in
          FStar_Syntax_Syntax.Tm_app uu____56048  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____56177 =
        let uu____56192 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____56211  ->
               match uu____56211 with
               | ({ FStar_Syntax_Syntax.ppname = uu____56222;
                    FStar_Syntax_Syntax.index = uu____56223;
                    FStar_Syntax_Syntax.sort = t;_},uu____56225)
                   ->
                   let uu____56233 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____56233) uu____56192
         in
      FStar_All.pipe_right bs uu____56177  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____56249 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____56267 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____56295 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____56316,uu____56317,bs,t,uu____56320,uu____56321)
                            ->
                            let uu____56330 = bs_univnames bs  in
                            let uu____56333 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____56330 uu____56333
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____56336,uu____56337,t,uu____56339,uu____56340,uu____56341)
                            -> FStar_Syntax_Free.univnames t
                        | uu____56348 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____56295 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_56357 = s  in
        let uu____56358 =
          let uu____56359 =
            let uu____56368 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____56386,bs,t,lids1,lids2) ->
                          let uu___1027_56399 = se  in
                          let uu____56400 =
                            let uu____56401 =
                              let uu____56418 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____56419 =
                                let uu____56420 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____56420 t  in
                              (lid, uvs, uu____56418, uu____56419, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____56401
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____56400;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_56399.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_56399.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_56399.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_56399.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____56434,t,tlid,n1,lids1) ->
                          let uu___1037_56445 = se  in
                          let uu____56446 =
                            let uu____56447 =
                              let uu____56463 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____56463, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____56447  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____56446;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_56445.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_56445.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_56445.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_56445.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____56467 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____56368, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____56359  in
        {
          FStar_Syntax_Syntax.sigel = uu____56358;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_56357.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_56357.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_56357.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_56357.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____56474,t) ->
        let uvs =
          let uu____56477 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____56477 FStar_Util.set_elements  in
        let uu___1046_56482 = s  in
        let uu____56483 =
          let uu____56484 =
            let uu____56491 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____56491)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____56484  in
        {
          FStar_Syntax_Syntax.sigel = uu____56483;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_56482.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_56482.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_56482.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_56482.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____56515 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____56518 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____56525) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____56558,(FStar_Util.Inl t,uu____56560),uu____56561)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____56608,(FStar_Util.Inr c,uu____56610),uu____56611)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____56658 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____56659,(FStar_Util.Inl t,uu____56661),uu____56662) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____56709,(FStar_Util.Inr c,uu____56711),uu____56712) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56759 -> empty_set  in
          FStar_Util.set_union uu____56515 uu____56518  in
        let all_lb_univs =
          let uu____56763 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56779 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56779) empty_set)
             in
          FStar_All.pipe_right uu____56763 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56789 = s  in
        let uu____56790 =
          let uu____56791 =
            let uu____56798 =
              let uu____56799 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56811 = lb  in
                        let uu____56812 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56815 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56811.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56812;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56811.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56815;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56811.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56811.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56799)  in
            (uu____56798, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56791  in
        {
          FStar_Syntax_Syntax.sigel = uu____56790;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56789.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56789.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56789.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56789.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56824,fml) ->
        let uvs =
          let uu____56827 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56827 FStar_Util.set_elements  in
        let uu___1112_56832 = s  in
        let uu____56833 =
          let uu____56834 =
            let uu____56841 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56841)  in
          FStar_Syntax_Syntax.Sig_assume uu____56834  in
        {
          FStar_Syntax_Syntax.sigel = uu____56833;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56832.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56832.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56832.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56832.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56843,bs,c,flags) ->
        let uvs =
          let uu____56852 =
            let uu____56855 = bs_univnames bs  in
            let uu____56858 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56855 uu____56858  in
          FStar_All.pipe_right uu____56852 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56866 = s  in
        let uu____56867 =
          let uu____56868 =
            let uu____56881 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56882 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56881, uu____56882, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56868  in
        {
          FStar_Syntax_Syntax.sigel = uu____56867;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56866.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56866.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56866.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56866.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56885 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56893  ->
    match uu___433_56893 with
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
    | uu____56944 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56965 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56965)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56991 =
      let uu____56992 = unparen t  in uu____56992.FStar_Parser_AST.tm  in
    match uu____56991 with
    | FStar_Parser_AST.Wild  ->
        let uu____56998 =
          let uu____56999 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56999  in
        FStar_Util.Inr uu____56998
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____57012)) ->
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
             let uu____57103 = sum_to_universe u n1  in
             FStar_Util.Inr uu____57103
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____57120 = sum_to_universe u n1  in
             FStar_Util.Inr uu____57120
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____57136 =
               let uu____57142 =
                 let uu____57144 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____57144
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____57142)
                in
             FStar_Errors.raise_error uu____57136 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____57153 ->
        let rec aux t1 univargs =
          let uu____57190 =
            let uu____57191 = unparen t1  in uu____57191.FStar_Parser_AST.tm
             in
          match uu____57190 with
          | FStar_Parser_AST.App (t2,targ,uu____57199) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_57226  ->
                     match uu___434_57226 with
                     | FStar_Util.Inr uu____57233 -> true
                     | uu____57236 -> false) univargs
              then
                let uu____57244 =
                  let uu____57245 =
                    FStar_List.map
                      (fun uu___435_57255  ->
                         match uu___435_57255 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____57245  in
                FStar_Util.Inr uu____57244
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_57281  ->
                        match uu___436_57281 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____57291 -> failwith "impossible")
                     univargs
                    in
                 let uu____57295 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____57295)
          | uu____57311 ->
              let uu____57312 =
                let uu____57318 =
                  let uu____57320 =
                    let uu____57322 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____57322 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____57320  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____57318)
                 in
              FStar_Errors.raise_error uu____57312 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____57337 ->
        let uu____57338 =
          let uu____57344 =
            let uu____57346 =
              let uu____57348 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____57348 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____57346  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____57344)  in
        FStar_Errors.raise_error uu____57338 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____57389;_});
            FStar_Syntax_Syntax.pos = uu____57390;
            FStar_Syntax_Syntax.vars = uu____57391;_})::uu____57392
        ->
        let uu____57423 =
          let uu____57429 =
            let uu____57431 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____57431
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____57429)  in
        FStar_Errors.raise_error uu____57423 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____57437 ->
        let uu____57456 =
          let uu____57462 =
            let uu____57464 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____57464
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____57462)  in
        FStar_Errors.raise_error uu____57456 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____57477 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____57477) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____57505 = FStar_List.hd fields  in
        match uu____57505 with
        | (f,uu____57515) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____57527 =
                match uu____57527 with
                | (f',uu____57533) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____57535 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____57535
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
              (let uu____57545 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____57545);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57908 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57915 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57916 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57918,pats1) ->
              let aux out uu____57959 =
                match uu____57959 with
                | (p2,uu____57972) ->
                    let intersection =
                      let uu____57982 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57982 out  in
                    let uu____57985 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57985
                    then
                      let uu____57990 = pat_vars p2  in
                      FStar_Util.set_union out uu____57990
                    else
                      (let duplicate_bv =
                         let uu____57996 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57996  in
                       let uu____57999 =
                         let uu____58005 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____58005)
                          in
                       FStar_Errors.raise_error uu____57999 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____58029 = pat_vars p1  in
            FStar_All.pipe_right uu____58029 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____58057 =
                let uu____58059 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____58059  in
              if uu____58057
              then ()
              else
                (let nonlinear_vars =
                   let uu____58068 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____58068  in
                 let first_nonlinear_var =
                   let uu____58072 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____58072  in
                 let uu____58075 =
                   let uu____58081 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____58081)  in
                 FStar_Errors.raise_error uu____58075 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____58109 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____58109 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____58126 ->
            let uu____58129 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____58129 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____58280 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____58304 =
              let uu____58305 =
                let uu____58306 =
                  let uu____58313 =
                    let uu____58314 =
                      let uu____58320 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____58320, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____58314  in
                  (uu____58313, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____58306  in
              {
                FStar_Parser_AST.pat = uu____58305;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____58304
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____58340 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____58343 = aux loc env1 p2  in
              match uu____58343 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_58432 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_58437 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_58437.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_58437.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_58432.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_58439 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_58444 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_58444.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_58444.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_58439.FStar_Syntax_Syntax.p)
                        }
                    | uu____58445 when top -> p4
                    | uu____58446 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____58451 =
                    match binder with
                    | LetBinder uu____58472 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____58497 = close_fun env1 t  in
                          desugar_term env1 uu____58497  in
                        let x1 =
                          let uu___1380_58499 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_58499.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_58499.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____58451 with
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
            let uu____58567 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____58567, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____58581 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____58581, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____58605 = resolvex loc env1 x  in
            (match uu____58605 with
             | (loc1,env2,xbv) ->
                 let uu____58634 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____58634, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____58657 = resolvex loc env1 x  in
            (match uu____58657 with
             | (loc1,env2,xbv) ->
                 let uu____58686 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____58686, [], imp))
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
            let uu____58701 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____58701, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____58731;_},args)
            ->
            let uu____58737 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58798  ->
                     match uu____58798 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58879 = aux loc1 env2 arg  in
                         (match uu____58879 with
                          | (loc2,env3,uu____58926,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58737 with
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
                 let uu____59058 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59058, annots, false))
        | FStar_Parser_AST.PatApp uu____59076 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____59107 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____59158  ->
                     match uu____59158 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____59219 = aux loc1 env2 pat  in
                         (match uu____59219 with
                          | (loc2,env3,uu____59261,pat1,ans,uu____59264) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____59107 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____59361 =
                     let uu____59364 =
                       let uu____59371 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____59371  in
                     let uu____59372 =
                       let uu____59373 =
                         let uu____59387 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____59387, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____59373  in
                     FStar_All.pipe_left uu____59364 uu____59372  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____59421 =
                            let uu____59422 =
                              let uu____59436 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____59436, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____59422  in
                          FStar_All.pipe_left (pos_r r) uu____59421) pats1
                     uu____59361
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
            let uu____59494 =
              FStar_List.fold_left
                (fun uu____59554  ->
                   fun p2  ->
                     match uu____59554 with
                     | (loc1,env2,annots,pats) ->
                         let uu____59636 = aux loc1 env2 p2  in
                         (match uu____59636 with
                          | (loc2,env3,uu____59683,pat,ans,uu____59686) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____59494 with
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
                   | uu____59852 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59855 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59855, annots, false))
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
                   (fun uu____59936  ->
                      match uu____59936 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59966  ->
                      match uu____59966 with
                      | (f,uu____59972) ->
                          let uu____59973 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59999  ->
                                    match uu____59999 with
                                    | (g,uu____60006) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59973 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____60012,p2) ->
                               p2)))
               in
            let app =
              let uu____60019 =
                let uu____60020 =
                  let uu____60027 =
                    let uu____60028 =
                      let uu____60029 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____60029  in
                    FStar_Parser_AST.mk_pattern uu____60028
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____60027, args)  in
                FStar_Parser_AST.PatApp uu____60020  in
              FStar_Parser_AST.mk_pattern uu____60019
                p1.FStar_Parser_AST.prange
               in
            let uu____60032 = aux loc env1 app  in
            (match uu____60032 with
             | (env2,e,b,p2,annots,uu____60078) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____60118 =
                         let uu____60119 =
                           let uu____60133 =
                             let uu___1528_60134 = fv  in
                             let uu____60135 =
                               let uu____60138 =
                                 let uu____60139 =
                                   let uu____60146 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____60146)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____60139
                                  in
                               FStar_Pervasives_Native.Some uu____60138  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_60134.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_60134.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____60135
                             }  in
                           (uu____60133, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____60119  in
                       FStar_All.pipe_left pos uu____60118
                   | uu____60172 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____60258 = aux' true loc env1 p2  in
            (match uu____60258 with
             | (loc1,env2,var,p3,ans,uu____60302) ->
                 let uu____60317 =
                   FStar_List.fold_left
                     (fun uu____60366  ->
                        fun p4  ->
                          match uu____60366 with
                          | (loc2,env3,ps1) ->
                              let uu____60431 = aux' true loc2 env3 p4  in
                              (match uu____60431 with
                               | (loc3,env4,uu____60472,p5,ans1,uu____60475)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____60317 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____60636 ->
            let uu____60637 = aux' true loc env1 p1  in
            (match uu____60637 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____60734 = aux_maybe_or env p  in
      match uu____60734 with
      | (env1,b,pats) ->
          ((let uu____60789 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60789
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
          let uu____60862 =
            let uu____60863 =
              let uu____60874 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60874, (ty, tacopt))  in
            LetBinder uu____60863  in
          (env, uu____60862, [])  in
        let op_to_ident x =
          let uu____60891 =
            let uu____60897 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60897, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60891  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60919 = op_to_ident x  in
              mklet uu____60919 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60921) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60927;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60943 = op_to_ident x  in
              let uu____60944 = desugar_term env t  in
              mklet uu____60943 uu____60944 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60946);
                 FStar_Parser_AST.prange = uu____60947;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60967 = desugar_term env t  in
              mklet x uu____60967 tacopt1
          | uu____60968 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60981 = desugar_data_pat env p  in
           match uu____60981 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____61010;
                      FStar_Syntax_Syntax.p = uu____61011;_},uu____61012)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____61025;
                      FStar_Syntax_Syntax.p = uu____61026;_},uu____61027)::[]
                     -> []
                 | uu____61040 -> p1  in
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
  fun uu____61048  ->
    fun env  ->
      fun pat  ->
        let uu____61052 = desugar_data_pat env pat  in
        match uu____61052 with | (env1,uu____61068,pat1) -> (env1, pat1)

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
      let uu____61090 = desugar_term_aq env e  in
      match uu____61090 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____61109 = desugar_typ_aq env e  in
      match uu____61109 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____61119  ->
        fun range  ->
          match uu____61119 with
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
              ((let uu____61141 =
                  let uu____61143 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____61143  in
                if uu____61141
                then
                  let uu____61146 =
                    let uu____61152 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____61152)  in
                  FStar_Errors.log_issue range uu____61146
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
                  let uu____61173 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____61173 range  in
                let lid1 =
                  let uu____61177 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____61177 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____61187 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____61187 range  in
                           let private_fv =
                             let uu____61189 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____61189 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_61190 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_61190.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_61190.FStar_Syntax_Syntax.vars)
                           }
                       | uu____61191 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____61195 =
                        let uu____61201 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____61201)
                         in
                      FStar_Errors.raise_error uu____61195 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____61221 =
                  let uu____61228 =
                    let uu____61229 =
                      let uu____61246 =
                        let uu____61257 =
                          let uu____61266 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____61266)  in
                        [uu____61257]  in
                      (lid1, uu____61246)  in
                    FStar_Syntax_Syntax.Tm_app uu____61229  in
                  FStar_Syntax_Syntax.mk uu____61228  in
                uu____61221 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____61314 =
          let uu____61315 = unparen t  in uu____61315.FStar_Parser_AST.tm  in
        match uu____61314 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____61316; FStar_Ident.ident = uu____61317;
              FStar_Ident.nsstr = uu____61318; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____61323 ->
            let uu____61324 =
              let uu____61330 =
                let uu____61332 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____61332  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____61330)  in
            FStar_Errors.raise_error uu____61324 t.FStar_Parser_AST.range
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
          let uu___1725_61419 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_61419.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_61419.FStar_Syntax_Syntax.vars)
          }  in
        let uu____61422 =
          let uu____61423 = unparen top  in uu____61423.FStar_Parser_AST.tm
           in
        match uu____61422 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____61428 ->
            let uu____61437 = desugar_formula env top  in
            (uu____61437, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____61446 = desugar_formula env t  in (uu____61446, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____61455 = desugar_formula env t  in (uu____61455, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____61482 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____61482, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____61484 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____61484, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____61493 =
                let uu____61494 =
                  let uu____61501 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____61501, args)  in
                FStar_Parser_AST.Op uu____61494  in
              FStar_Parser_AST.mk_term uu____61493 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____61506 =
              let uu____61507 =
                let uu____61508 =
                  let uu____61515 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____61515, [e])  in
                FStar_Parser_AST.Op uu____61508  in
              FStar_Parser_AST.mk_term uu____61507 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____61506
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____61527 = FStar_Ident.text_of_id op_star  in
             uu____61527 = "*") &&
              (let uu____61532 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____61532 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____61549;_},t1::t2::[])
                  when
                  let uu____61555 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____61555 FStar_Option.isNone ->
                  let uu____61562 = flatten1 t1  in
                  FStar_List.append uu____61562 [t2]
              | uu____61565 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_61570 = top  in
              let uu____61571 =
                let uu____61572 =
                  let uu____61583 =
                    FStar_List.map (fun _61594  -> FStar_Util.Inr _61594)
                      terms
                     in
                  (uu____61583, rhs)  in
                FStar_Parser_AST.Sum uu____61572  in
              {
                FStar_Parser_AST.tm = uu____61571;
                FStar_Parser_AST.range =
                  (uu___1773_61570.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_61570.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____61602 =
              let uu____61603 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____61603  in
            (uu____61602, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____61609 =
              let uu____61615 =
                let uu____61617 =
                  let uu____61619 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____61619 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____61617  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____61615)
               in
            FStar_Errors.raise_error uu____61609 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____61634 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____61634 with
             | FStar_Pervasives_Native.None  ->
                 let uu____61641 =
                   let uu____61647 =
                     let uu____61649 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____61649
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____61647)
                    in
                 FStar_Errors.raise_error uu____61641
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____61664 =
                     let uu____61689 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61751 = desugar_term_aq env t  in
                               match uu____61751 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____61689 FStar_List.unzip  in
                   (match uu____61664 with
                    | (args1,aqs) ->
                        let uu____61884 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61884, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61901)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61918 =
              let uu___1802_61919 = top  in
              let uu____61920 =
                let uu____61921 =
                  let uu____61928 =
                    let uu___1804_61929 = top  in
                    let uu____61930 =
                      let uu____61931 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61931  in
                    {
                      FStar_Parser_AST.tm = uu____61930;
                      FStar_Parser_AST.range =
                        (uu___1804_61929.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61929.FStar_Parser_AST.level)
                    }  in
                  (uu____61928, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61921  in
              {
                FStar_Parser_AST.tm = uu____61920;
                FStar_Parser_AST.range =
                  (uu___1802_61919.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61919.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61918
        | FStar_Parser_AST.Construct (n1,(a,uu____61939)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61959 =
                let uu___1814_61960 = top  in
                let uu____61961 =
                  let uu____61962 =
                    let uu____61969 =
                      let uu___1816_61970 = top  in
                      let uu____61971 =
                        let uu____61972 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61972  in
                      {
                        FStar_Parser_AST.tm = uu____61971;
                        FStar_Parser_AST.range =
                          (uu___1816_61970.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61970.FStar_Parser_AST.level)
                      }  in
                    (uu____61969, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61962  in
                {
                  FStar_Parser_AST.tm = uu____61961;
                  FStar_Parser_AST.range =
                    (uu___1814_61960.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61960.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61959))
        | FStar_Parser_AST.Construct (n1,(a,uu____61980)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61997 =
              let uu___1825_61998 = top  in
              let uu____61999 =
                let uu____62000 =
                  let uu____62007 =
                    let uu___1827_62008 = top  in
                    let uu____62009 =
                      let uu____62010 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____62010  in
                    {
                      FStar_Parser_AST.tm = uu____62009;
                      FStar_Parser_AST.range =
                        (uu___1827_62008.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_62008.FStar_Parser_AST.level)
                    }  in
                  (uu____62007, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____62000  in
              {
                FStar_Parser_AST.tm = uu____61999;
                FStar_Parser_AST.range =
                  (uu___1825_61998.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61998.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61997
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____62016; FStar_Ident.ident = uu____62017;
              FStar_Ident.nsstr = uu____62018; FStar_Ident.str = "Type0";_}
            ->
            let uu____62023 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____62023, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____62024; FStar_Ident.ident = uu____62025;
              FStar_Ident.nsstr = uu____62026; FStar_Ident.str = "Type";_}
            ->
            let uu____62031 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____62031, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____62032; FStar_Ident.ident = uu____62033;
               FStar_Ident.nsstr = uu____62034; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____62054 =
              let uu____62055 =
                let uu____62056 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____62056  in
              mk1 uu____62055  in
            (uu____62054, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____62057; FStar_Ident.ident = uu____62058;
              FStar_Ident.nsstr = uu____62059; FStar_Ident.str = "Effect";_}
            ->
            let uu____62064 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____62064, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____62065; FStar_Ident.ident = uu____62066;
              FStar_Ident.nsstr = uu____62067; FStar_Ident.str = "True";_}
            ->
            let uu____62072 =
              let uu____62073 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____62073
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____62072, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____62074; FStar_Ident.ident = uu____62075;
              FStar_Ident.nsstr = uu____62076; FStar_Ident.str = "False";_}
            ->
            let uu____62081 =
              let uu____62082 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____62082
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____62081, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____62085;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____62088 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____62088 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____62097 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____62097, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____62099 =
                    let uu____62101 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____62101 txt
                     in
                  failwith uu____62099))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____62110 = desugar_name mk1 setpos env true l  in
              (uu____62110, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____62119 = desugar_name mk1 setpos env true l  in
              (uu____62119, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____62137 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____62137 with
                | FStar_Pervasives_Native.Some uu____62147 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____62155 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____62155 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____62173 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____62194 =
                    let uu____62195 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____62195  in
                  (uu____62194, noaqs)
              | uu____62201 ->
                  let uu____62209 =
                    let uu____62215 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____62215)  in
                  FStar_Errors.raise_error uu____62209
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____62225 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____62225 with
              | FStar_Pervasives_Native.None  ->
                  let uu____62232 =
                    let uu____62238 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____62238)
                     in
                  FStar_Errors.raise_error uu____62232
                    top.FStar_Parser_AST.range
              | uu____62246 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____62250 = desugar_name mk1 setpos env true lid'  in
                  (uu____62250, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____62272 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____62272 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____62291 ->
                       let uu____62298 =
                         FStar_Util.take
                           (fun uu____62322  ->
                              match uu____62322 with
                              | (uu____62328,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____62298 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____62373 =
                              let uu____62398 =
                                FStar_List.map
                                  (fun uu____62441  ->
                                     match uu____62441 with
                                     | (t,imp) ->
                                         let uu____62458 =
                                           desugar_term_aq env t  in
                                         (match uu____62458 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____62398
                                FStar_List.unzip
                               in
                            (match uu____62373 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____62601 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____62601, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____62620 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____62620 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____62631 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_62659  ->
                 match uu___437_62659 with
                 | FStar_Util.Inr uu____62665 -> true
                 | uu____62667 -> false) binders
            ->
            let terms =
              let uu____62676 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_62693  ->
                        match uu___438_62693 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____62699 -> failwith "Impossible"))
                 in
              FStar_List.append uu____62676 [t]  in
            let uu____62701 =
              let uu____62726 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62783 = desugar_typ_aq env t1  in
                        match uu____62783 with
                        | (t',aq) ->
                            let uu____62794 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62794, aq)))
                 in
              FStar_All.pipe_right uu____62726 FStar_List.unzip  in
            (match uu____62701 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62904 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62904
                    in
                 let uu____62913 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62913, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62940 =
              let uu____62957 =
                let uu____62964 =
                  let uu____62971 =
                    FStar_All.pipe_left
                      (fun _62980  -> FStar_Util.Inl _62980)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62971]  in
                FStar_List.append binders uu____62964  in
              FStar_List.fold_left
                (fun uu____63025  ->
                   fun b  ->
                     match uu____63025 with
                     | (env1,tparams,typs) ->
                         let uu____63086 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____63101 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____63101)
                            in
                         (match uu____63086 with
                          | (xopt,t1) ->
                              let uu____63126 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____63135 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____63135)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____63126 with
                               | (env2,x) ->
                                   let uu____63155 =
                                     let uu____63158 =
                                       let uu____63161 =
                                         let uu____63162 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____63162
                                          in
                                       [uu____63161]  in
                                     FStar_List.append typs uu____63158  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_63188 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_63188.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_63188.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____63155)))) (env, [], [])
                uu____62957
               in
            (match uu____62940 with
             | (env1,uu____63216,targs) ->
                 let tup =
                   let uu____63239 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____63239
                    in
                 let uu____63240 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____63240, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____63259 = uncurry binders t  in
            (match uu____63259 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_63303 =
                   match uu___439_63303 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____63320 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____63320
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____63344 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____63344 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____63377 = aux env [] bs  in (uu____63377, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____63386 = desugar_binder env b  in
            (match uu____63386 with
             | (FStar_Pervasives_Native.None ,uu____63397) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____63412 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____63412 with
                  | ((x,uu____63428),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____63441 =
                        let uu____63442 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____63442  in
                      (uu____63441, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____63521 = FStar_Util.set_is_empty i  in
                    if uu____63521
                    then
                      let uu____63526 = FStar_Util.set_union acc set1  in
                      aux uu____63526 sets2
                    else
                      (let uu____63531 =
                         let uu____63532 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____63532  in
                       FStar_Pervasives_Native.Some uu____63531)
                 in
              let uu____63535 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____63535 sets  in
            ((let uu____63539 = check_disjoint bvss  in
              match uu____63539 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____63543 =
                    let uu____63549 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____63549)
                     in
                  let uu____63553 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____63543 uu____63553);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____63561 =
                FStar_List.fold_left
                  (fun uu____63581  ->
                     fun pat  ->
                       match uu____63581 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____63607,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____63617 =
                                  let uu____63620 = free_type_vars env1 t  in
                                  FStar_List.append uu____63620 ftvs  in
                                (env1, uu____63617)
                            | FStar_Parser_AST.PatAscribed
                                (uu____63625,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____63636 =
                                  let uu____63639 = free_type_vars env1 t  in
                                  let uu____63642 =
                                    let uu____63645 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____63645 ftvs  in
                                  FStar_List.append uu____63639 uu____63642
                                   in
                                (env1, uu____63636)
                            | uu____63650 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____63561 with
              | (uu____63659,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____63671 =
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
                    FStar_List.append uu____63671 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_63728 =
                    match uu___440_63728 with
                    | [] ->
                        let uu____63755 = desugar_term_aq env1 body  in
                        (match uu____63755 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63792 =
                                       let uu____63793 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63793
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63792
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
                             let uu____63862 =
                               let uu____63865 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63865  in
                             (uu____63862, aq))
                    | p::rest ->
                        let uu____63880 = desugar_binding_pat env1 p  in
                        (match uu____63880 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63914)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63929 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63938 =
                               match b with
                               | LetBinder uu____63979 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____64048) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____64102 =
                                           let uu____64111 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____64111, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____64102
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____64173,uu____64174) ->
                                              let tup2 =
                                                let uu____64176 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____64176
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____64181 =
                                                  let uu____64188 =
                                                    let uu____64189 =
                                                      let uu____64206 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____64209 =
                                                        let uu____64220 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____64229 =
                                                          let uu____64240 =
                                                            let uu____64249 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____64249
                                                             in
                                                          [uu____64240]  in
                                                        uu____64220 ::
                                                          uu____64229
                                                         in
                                                      (uu____64206,
                                                        uu____64209)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____64189
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____64188
                                                   in
                                                uu____64181
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____64297 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____64297
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____64348,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____64350,pats)) ->
                                              let tupn =
                                                let uu____64395 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____64395
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____64408 =
                                                  let uu____64409 =
                                                    let uu____64426 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____64429 =
                                                      let uu____64440 =
                                                        let uu____64451 =
                                                          let uu____64460 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____64460
                                                           in
                                                        [uu____64451]  in
                                                      FStar_List.append args
                                                        uu____64440
                                                       in
                                                    (uu____64426,
                                                      uu____64429)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____64409
                                                   in
                                                mk1 uu____64408  in
                                              let p2 =
                                                let uu____64508 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____64508
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____64555 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63938 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____64649,uu____64650,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____64672 =
                let uu____64673 = unparen e  in
                uu____64673.FStar_Parser_AST.tm  in
              match uu____64672 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____64683 ->
                  let uu____64684 = desugar_term_aq env e  in
                  (match uu____64684 with
                   | (head1,aq) ->
                       let uu____64697 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____64697, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____64704 ->
            let rec aux args aqs e =
              let uu____64781 =
                let uu____64782 = unparen e  in
                uu____64782.FStar_Parser_AST.tm  in
              match uu____64781 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64800 = desugar_term_aq env t  in
                  (match uu____64800 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64848 ->
                  let uu____64849 = desugar_term_aq env e  in
                  (match uu____64849 with
                   | (head1,aq) ->
                       let uu____64870 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64870, (join_aqs (aq :: aqs))))
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
            let uu____64933 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64933
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
            let uu____64985 = desugar_term_aq env t  in
            (match uu____64985 with
             | (tm,s) ->
                 let uu____64996 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64996, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____65002 =
              let uu____65015 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____65015 then desugar_typ_aq else desugar_term_aq  in
            uu____65002 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____65074 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____65217  ->
                        match uu____65217 with
                        | (attr_opt,(p,def)) ->
                            let uu____65275 = is_app_pattern p  in
                            if uu____65275
                            then
                              let uu____65308 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____65308, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____65391 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____65391, def1)
                               | uu____65436 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____65474);
                                           FStar_Parser_AST.prange =
                                             uu____65475;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____65524 =
                                            let uu____65545 =
                                              let uu____65550 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____65550  in
                                            (uu____65545, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____65524, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____65642) ->
                                        if top_level
                                        then
                                          let uu____65678 =
                                            let uu____65699 =
                                              let uu____65704 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____65704  in
                                            (uu____65699, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____65678, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65795 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65828 =
                FStar_List.fold_left
                  (fun uu____65901  ->
                     fun uu____65902  ->
                       match (uu____65901, uu____65902) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____66010,uu____66011),uu____66012))
                           ->
                           let uu____66129 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____66155 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____66155 with
                                  | (env2,xx) ->
                                      let uu____66174 =
                                        let uu____66177 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____66177 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____66174))
                             | FStar_Util.Inr l ->
                                 let uu____66185 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____66185, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____66129 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65828 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____66333 =
                    match uu____66333 with
                    | (attrs_opt,(uu____66369,args,result_t),def) ->
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
                                let uu____66457 = is_comp_type env1 t  in
                                if uu____66457
                                then
                                  ((let uu____66461 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____66471 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____66471))
                                       in
                                    match uu____66461 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____66478 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____66481 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____66481))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____66478
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
                          | uu____66492 ->
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
                              let uu____66507 =
                                let uu____66508 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____66508
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____66507
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
                  let uu____66589 = desugar_term_aq env' body  in
                  (match uu____66589 with
                   | (body1,aq) ->
                       let uu____66602 =
                         let uu____66605 =
                           let uu____66606 =
                             let uu____66620 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____66620)  in
                           FStar_Syntax_Syntax.Tm_let uu____66606  in
                         FStar_All.pipe_left mk1 uu____66605  in
                       (uu____66602, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____66695 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____66695 with
              | (env1,binder,pat1) ->
                  let uu____66717 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66743 = desugar_term_aq env1 t2  in
                        (match uu____66743 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66757 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66757
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66758 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66758, aq))
                    | LocalBinder (x,uu____66791) ->
                        let uu____66792 = desugar_term_aq env1 t2  in
                        (match uu____66792 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66806;
                                    FStar_Syntax_Syntax.p = uu____66807;_},uu____66808)::[]
                                   -> body1
                               | uu____66821 ->
                                   let uu____66824 =
                                     let uu____66831 =
                                       let uu____66832 =
                                         let uu____66855 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66858 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66855, uu____66858)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66832
                                        in
                                     FStar_Syntax_Syntax.mk uu____66831  in
                                   uu____66824 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66895 =
                               let uu____66898 =
                                 let uu____66899 =
                                   let uu____66913 =
                                     let uu____66916 =
                                       let uu____66917 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66917]  in
                                     FStar_Syntax_Subst.close uu____66916
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66913)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66899  in
                               FStar_All.pipe_left mk1 uu____66898  in
                             (uu____66895, aq))
                     in
                  (match uu____66717 with | (tm,aq) -> (tm, aq))
               in
            let uu____66979 = FStar_List.hd lbs  in
            (match uu____66979 with
             | (attrs,(head_pat,defn)) ->
                 let uu____67023 = is_rec || (is_app_pattern head_pat)  in
                 if uu____67023
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____67039 =
                let uu____67040 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____67040  in
              mk1 uu____67039  in
            let uu____67041 = desugar_term_aq env t1  in
            (match uu____67041 with
             | (t1',aq1) ->
                 let uu____67052 = desugar_term_aq env t2  in
                 (match uu____67052 with
                  | (t2',aq2) ->
                      let uu____67063 = desugar_term_aq env t3  in
                      (match uu____67063 with
                       | (t3',aq3) ->
                           let uu____67074 =
                             let uu____67075 =
                               let uu____67076 =
                                 let uu____67099 =
                                   let uu____67116 =
                                     let uu____67131 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____67131,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____67145 =
                                     let uu____67162 =
                                       let uu____67177 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____67177,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____67162]  in
                                   uu____67116 :: uu____67145  in
                                 (t1', uu____67099)  in
                               FStar_Syntax_Syntax.Tm_match uu____67076  in
                             mk1 uu____67075  in
                           (uu____67074, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____67373 =
              match uu____67373 with
              | (pat,wopt,b) ->
                  let uu____67395 = desugar_match_pat env pat  in
                  (match uu____67395 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____67426 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____67426
                          in
                       let uu____67431 = desugar_term_aq env1 b  in
                       (match uu____67431 with
                        | (b1,aq) ->
                            let uu____67444 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____67444, aq)))
               in
            let uu____67449 = desugar_term_aq env e  in
            (match uu____67449 with
             | (e1,aq) ->
                 let uu____67460 =
                   let uu____67491 =
                     let uu____67524 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____67524 FStar_List.unzip  in
                   FStar_All.pipe_right uu____67491
                     (fun uu____67742  ->
                        match uu____67742 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____67460 with
                  | (brs,aqs) ->
                      let uu____67961 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67961, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67995 =
              let uu____68016 = is_comp_type env t  in
              if uu____68016
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____68071 = desugar_term_aq env t  in
                 match uu____68071 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67995 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____68163 = desugar_term_aq env e  in
                 (match uu____68163 with
                  | (e1,aq) ->
                      let uu____68174 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____68174, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____68213,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____68256 = FStar_List.hd fields  in
              match uu____68256 with | (f,uu____68268) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____68314  ->
                        match uu____68314 with
                        | (g,uu____68321) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____68328,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____68342 =
                         let uu____68348 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____68348)
                          in
                       FStar_Errors.raise_error uu____68342
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
                  let uu____68359 =
                    let uu____68370 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____68401  ->
                              match uu____68401 with
                              | (f,uu____68411) ->
                                  let uu____68412 =
                                    let uu____68413 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____68413
                                     in
                                  (uu____68412, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____68370)  in
                  FStar_Parser_AST.Construct uu____68359
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____68431 =
                      let uu____68432 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____68432  in
                    FStar_Parser_AST.mk_term uu____68431
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____68434 =
                      let uu____68447 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____68477  ->
                                match uu____68477 with
                                | (f,uu____68487) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____68447)  in
                    FStar_Parser_AST.Record uu____68434  in
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
            let uu____68547 = desugar_term_aq env recterm1  in
            (match uu____68547 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____68563;
                         FStar_Syntax_Syntax.vars = uu____68564;_},args)
                      ->
                      let uu____68590 =
                        let uu____68591 =
                          let uu____68592 =
                            let uu____68609 =
                              let uu____68612 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____68613 =
                                let uu____68616 =
                                  let uu____68617 =
                                    let uu____68624 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____68624)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____68617
                                   in
                                FStar_Pervasives_Native.Some uu____68616  in
                              FStar_Syntax_Syntax.fvar uu____68612
                                FStar_Syntax_Syntax.delta_constant
                                uu____68613
                               in
                            (uu____68609, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____68592  in
                        FStar_All.pipe_left mk1 uu____68591  in
                      (uu____68590, s)
                  | uu____68653 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____68657 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____68657 with
              | (constrname,is_rec) ->
                  let uu____68676 = desugar_term_aq env e  in
                  (match uu____68676 with
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
                       let uu____68696 =
                         let uu____68697 =
                           let uu____68698 =
                             let uu____68715 =
                               let uu____68718 =
                                 let uu____68719 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____68719
                                  in
                               FStar_Syntax_Syntax.fvar uu____68718
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____68721 =
                               let uu____68732 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____68732]  in
                             (uu____68715, uu____68721)  in
                           FStar_Syntax_Syntax.Tm_app uu____68698  in
                         FStar_All.pipe_left mk1 uu____68697  in
                       (uu____68696, s))))
        | FStar_Parser_AST.NamedTyp (uu____68769,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68779 =
              let uu____68780 = FStar_Syntax_Subst.compress tm  in
              uu____68780.FStar_Syntax_Syntax.n  in
            (match uu____68779 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68788 =
                   let uu___2520_68789 =
                     let uu____68790 =
                       let uu____68792 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68792  in
                     FStar_Syntax_Util.exp_string uu____68790  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68789.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68789.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68788, noaqs)
             | uu____68793 ->
                 let uu____68794 =
                   let uu____68800 =
                     let uu____68802 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68802
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68800)  in
                 FStar_Errors.raise_error uu____68794
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68811 = desugar_term_aq env e  in
            (match uu____68811 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68823 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68823, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68828 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68829 =
              let uu____68830 =
                let uu____68837 = desugar_term env e  in (bv, uu____68837)
                 in
              [uu____68830]  in
            (uu____68828, uu____68829)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68862 =
              let uu____68863 =
                let uu____68864 =
                  let uu____68871 = desugar_term env e  in (uu____68871, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68864  in
              FStar_All.pipe_left mk1 uu____68863  in
            (uu____68862, noaqs)
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
              let uu____68900 =
                let uu____68901 =
                  let uu____68908 =
                    let uu____68909 =
                      let uu____68910 =
                        let uu____68919 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68932 =
                          let uu____68933 =
                            let uu____68934 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68934  in
                          FStar_Parser_AST.mk_term uu____68933
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68919, uu____68932,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68910  in
                    FStar_Parser_AST.mk_term uu____68909
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68908)  in
                FStar_Parser_AST.Abs uu____68901  in
              FStar_Parser_AST.mk_term uu____68900
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
                   fun uu____68980  ->
                     match uu____68980 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68984 =
                           let uu____68991 =
                             let uu____68996 = eta_and_annot rel2  in
                             (uu____68996, FStar_Parser_AST.Nothing)  in
                           let uu____68997 =
                             let uu____69004 =
                               let uu____69011 =
                                 let uu____69016 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____69016, FStar_Parser_AST.Nothing)  in
                               let uu____69017 =
                                 let uu____69024 =
                                   let uu____69029 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____69029, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____69024]  in
                               uu____69011 :: uu____69017  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____69004
                              in
                           uu____68991 :: uu____68997  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68984
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____69051 =
                let uu____69058 =
                  let uu____69063 = FStar_Parser_AST.thunk e1  in
                  (uu____69063, FStar_Parser_AST.Nothing)  in
                [uu____69058]  in
              FStar_Parser_AST.mkApp finish1 uu____69051
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____69072 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____69073 = desugar_formula env top  in
            (uu____69073, noaqs)
        | uu____69074 ->
            let uu____69075 =
              let uu____69081 =
                let uu____69083 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____69083  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____69081)  in
            FStar_Errors.raise_error uu____69075 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____69093 -> false
    | uu____69103 -> true

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
           (fun uu____69141  ->
              match uu____69141 with
              | (a,imp) ->
                  let uu____69154 = desugar_term env a  in
                  arg_withimp_e imp uu____69154))

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
          let is_requires uu____69191 =
            match uu____69191 with
            | (t1,uu____69198) ->
                let uu____69199 =
                  let uu____69200 = unparen t1  in
                  uu____69200.FStar_Parser_AST.tm  in
                (match uu____69199 with
                 | FStar_Parser_AST.Requires uu____69202 -> true
                 | uu____69211 -> false)
             in
          let is_ensures uu____69223 =
            match uu____69223 with
            | (t1,uu____69230) ->
                let uu____69231 =
                  let uu____69232 = unparen t1  in
                  uu____69232.FStar_Parser_AST.tm  in
                (match uu____69231 with
                 | FStar_Parser_AST.Ensures uu____69234 -> true
                 | uu____69243 -> false)
             in
          let is_app head1 uu____69261 =
            match uu____69261 with
            | (t1,uu____69269) ->
                let uu____69270 =
                  let uu____69271 = unparen t1  in
                  uu____69271.FStar_Parser_AST.tm  in
                (match uu____69270 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____69274;
                        FStar_Parser_AST.level = uu____69275;_},uu____69276,uu____69277)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____69279 -> false)
             in
          let is_smt_pat uu____69291 =
            match uu____69291 with
            | (t1,uu____69298) ->
                let uu____69299 =
                  let uu____69300 = unparen t1  in
                  uu____69300.FStar_Parser_AST.tm  in
                (match uu____69299 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____69304);
                               FStar_Parser_AST.range = uu____69305;
                               FStar_Parser_AST.level = uu____69306;_},uu____69307)::uu____69308::[])
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
                               FStar_Parser_AST.range = uu____69357;
                               FStar_Parser_AST.level = uu____69358;_},uu____69359)::uu____69360::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____69393 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____69428 = head_and_args t1  in
            match uu____69428 with
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
                     let thunk_ens uu____69521 =
                       match uu____69521 with
                       | (e,i) ->
                           let uu____69532 = FStar_Parser_AST.thunk e  in
                           (uu____69532, i)
                        in
                     let fail_lemma uu____69544 =
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
                           let uu____69650 =
                             let uu____69657 =
                               let uu____69664 = thunk_ens ens  in
                               [uu____69664; nil_pat]  in
                             req_true :: uu____69657  in
                           unit_tm :: uu____69650
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____69711 =
                             let uu____69718 =
                               let uu____69725 = thunk_ens ens  in
                               [uu____69725; nil_pat]  in
                             req :: uu____69718  in
                           unit_tm :: uu____69711
                       | ens::smtpat::[] when
                           (((let uu____69774 = is_requires ens  in
                              Prims.op_Negation uu____69774) &&
                               (let uu____69777 = is_smt_pat ens  in
                                Prims.op_Negation uu____69777))
                              &&
                              (let uu____69780 = is_decreases ens  in
                               Prims.op_Negation uu____69780))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69782 =
                             let uu____69789 =
                               let uu____69796 = thunk_ens ens  in
                               [uu____69796; smtpat]  in
                             req_true :: uu____69789  in
                           unit_tm :: uu____69782
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69843 =
                             let uu____69850 =
                               let uu____69857 = thunk_ens ens  in
                               [uu____69857; nil_pat; dec]  in
                             req_true :: uu____69850  in
                           unit_tm :: uu____69843
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69917 =
                             let uu____69924 =
                               let uu____69931 = thunk_ens ens  in
                               [uu____69931; smtpat; dec]  in
                             req_true :: uu____69924  in
                           unit_tm :: uu____69917
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69991 =
                             let uu____69998 =
                               let uu____70005 = thunk_ens ens  in
                               [uu____70005; nil_pat; dec]  in
                             req :: uu____69998  in
                           unit_tm :: uu____69991
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____70065 =
                             let uu____70072 =
                               let uu____70079 = thunk_ens ens  in
                               [uu____70079; smtpat]  in
                             req :: uu____70072  in
                           unit_tm :: uu____70065
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____70144 =
                             let uu____70151 =
                               let uu____70158 = thunk_ens ens  in
                               [uu____70158; dec; smtpat]  in
                             req :: uu____70151  in
                           unit_tm :: uu____70144
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____70220 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____70220, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____70248 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____70248
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____70251 =
                       let uu____70258 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____70258, [])  in
                     (uu____70251, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____70276 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____70276
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____70279 =
                       let uu____70286 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____70286, [])  in
                     (uu____70279, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____70308 =
                       let uu____70315 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____70315, [])  in
                     (uu____70308, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____70338 when allow_type_promotion ->
                     let default_effect =
                       let uu____70340 = FStar_Options.ml_ish ()  in
                       if uu____70340
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____70346 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____70346
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____70353 =
                       let uu____70360 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____70360, [])  in
                     (uu____70353, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____70383 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____70402 = pre_process_comp_typ t  in
          match uu____70402 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____70454 =
                    let uu____70460 =
                      let uu____70462 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____70462
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____70460)
                     in
                  fail1 uu____70454)
               else ();
               (let is_universe uu____70478 =
                  match uu____70478 with
                  | (uu____70484,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____70486 = FStar_Util.take is_universe args  in
                match uu____70486 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____70545  ->
                           match uu____70545 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____70552 =
                      let uu____70567 = FStar_List.hd args1  in
                      let uu____70576 = FStar_List.tl args1  in
                      (uu____70567, uu____70576)  in
                    (match uu____70552 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____70631 =
                           let is_decrease uu____70670 =
                             match uu____70670 with
                             | (t1,uu____70681) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____70692;
                                         FStar_Syntax_Syntax.vars =
                                           uu____70693;_},uu____70694::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____70733 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____70631 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70850  ->
                                        match uu____70850 with
                                        | (t1,uu____70860) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70869,(arg,uu____70871)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70910 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70931 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70943 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70943
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70950 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70950
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70960 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70960
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70967 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70967
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70974 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70974
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70981 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70981
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____71002 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____71002
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
                                                    let uu____71093 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____71093
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
                                              | uu____71114 -> pat  in
                                            let uu____71115 =
                                              let uu____71126 =
                                                let uu____71137 =
                                                  let uu____71146 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____71146, aq)  in
                                                [uu____71137]  in
                                              ens :: uu____71126  in
                                            req :: uu____71115
                                        | uu____71187 -> rest2
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
        | uu____71219 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_71241 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_71241.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_71241.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_71283 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_71283.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_71283.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_71283.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____71346 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____71346)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71359 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71359 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_71369 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_71369.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_71369.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____71395 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____71409 =
                     let uu____71412 =
                       let uu____71413 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____71413]  in
                     no_annot_abs uu____71412 body2  in
                   FStar_All.pipe_left setpos uu____71409  in
                 let uu____71434 =
                   let uu____71435 =
                     let uu____71452 =
                       let uu____71455 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____71455
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____71457 =
                       let uu____71468 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____71468]  in
                     (uu____71452, uu____71457)  in
                   FStar_Syntax_Syntax.Tm_app uu____71435  in
                 FStar_All.pipe_left mk1 uu____71434)
        | uu____71507 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____71588 = q (rest, pats, body)  in
              let uu____71595 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____71588 uu____71595
                FStar_Parser_AST.Formula
               in
            let uu____71596 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____71596 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____71605 -> failwith "impossible"  in
      let uu____71609 =
        let uu____71610 = unparen f  in uu____71610.FStar_Parser_AST.tm  in
      match uu____71609 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____71623,uu____71624) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____71636,uu____71637) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____71669 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____71669
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____71705 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____71705
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71749 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71754 =
        FStar_List.fold_left
          (fun uu____71787  ->
             fun b  ->
               match uu____71787 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71831 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71831.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71831.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71831.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71846 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71846 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71864 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71864.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71864.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71865 =
                               let uu____71872 =
                                 let uu____71877 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71877)  in
                               uu____71872 :: out  in
                             (env2, uu____71865))
                    | uu____71888 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71754 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71961 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71961)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71966 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71966)
      | FStar_Parser_AST.TVariable x ->
          let uu____71970 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71970)
      | FStar_Parser_AST.NoName t ->
          let uu____71974 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71974)
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
      fun uu___441_71982  ->
        match uu___441_71982 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____72004 = FStar_Syntax_Syntax.null_binder k  in
            (uu____72004, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____72021 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____72021 with
             | (env1,a1) ->
                 let uu____72038 =
                   let uu____72045 = trans_aqual env1 imp  in
                   ((let uu___2962_72051 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_72051.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_72051.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____72045)
                    in
                 (uu____72038, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_72059  ->
      match uu___442_72059 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____72063 =
            let uu____72064 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____72064  in
          FStar_Pervasives_Native.Some uu____72063
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____72080) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____72082) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____72085 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____72103 = binder_ident b  in
         FStar_Common.list_of_option uu____72103) bs
  
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
               (fun uu___443_72140  ->
                  match uu___443_72140 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____72145 -> false))
           in
        let quals2 q =
          let uu____72159 =
            (let uu____72163 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____72163) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____72159
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____72180 = FStar_Ident.range_of_lid disc_name  in
                let uu____72181 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____72180;
                  FStar_Syntax_Syntax.sigquals = uu____72181;
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
            let uu____72221 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____72259  ->
                        match uu____72259 with
                        | (x,uu____72270) ->
                            let uu____72275 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____72275 with
                             | (field_name,uu____72283) ->
                                 let only_decl =
                                   ((let uu____72288 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____72288)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____72290 =
                                        let uu____72292 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____72292.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____72290)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____72310 =
                                       FStar_List.filter
                                         (fun uu___444_72314  ->
                                            match uu___444_72314 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____72317 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____72310
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_72332  ->
                                             match uu___445_72332 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____72337 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____72340 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____72340;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____72347 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____72347
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____72358 =
                                        let uu____72363 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____72363  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____72358;
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
                                      let uu____72367 =
                                        let uu____72368 =
                                          let uu____72375 =
                                            let uu____72378 =
                                              let uu____72379 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____72379
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____72378]  in
                                          ((false, [lb]), uu____72375)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____72368
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____72367;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____72221 FStar_List.flatten
  
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
            (lid,uu____72428,t,uu____72430,n1,uu____72432) when
            let uu____72439 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____72439 ->
            let uu____72441 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____72441 with
             | (formals,uu____72459) ->
                 (match formals with
                  | [] -> []
                  | uu____72488 ->
                      let filter_records uu___446_72504 =
                        match uu___446_72504 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____72507,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____72519 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____72521 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____72521 with
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
                      let uu____72533 = FStar_Util.first_N n1 formals  in
                      (match uu____72533 with
                       | (uu____72562,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____72596 -> []
  
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
                    let uu____72675 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____72675
                    then
                      let uu____72681 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____72681
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____72685 =
                      let uu____72690 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____72690  in
                    let uu____72691 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____72697 =
                          let uu____72700 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____72700  in
                        FStar_Syntax_Util.arrow typars uu____72697
                      else FStar_Syntax_Syntax.tun  in
                    let uu____72705 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____72685;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____72691;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____72705;
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
          let tycon_id uu___447_72759 =
            match uu___447_72759 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72761,uu____72762) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72772,uu____72773,uu____72774) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72784,uu____72785,uu____72786) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72816,uu____72817,uu____72818) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72864) ->
                let uu____72865 =
                  let uu____72866 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72866  in
                FStar_Parser_AST.mk_term uu____72865 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72868 =
                  let uu____72869 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72869  in
                FStar_Parser_AST.mk_term uu____72868 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72871) ->
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
              | uu____72902 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72910 =
                     let uu____72911 =
                       let uu____72918 = binder_to_term b  in
                       (out, uu____72918, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72911  in
                   FStar_Parser_AST.mk_term uu____72910
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72930 =
            match uu___448_72930 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72987  ->
                       match uu____72987 with
                       | (x,t,uu____72998) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____73004 =
                    let uu____73005 =
                      let uu____73006 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____73006  in
                    FStar_Parser_AST.mk_term uu____73005
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____73004 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____73013 = binder_idents parms  in id1 ::
                    uu____73013
                   in
                (FStar_List.iter
                   (fun uu____73031  ->
                      match uu____73031 with
                      | (f,uu____73041,uu____73042) ->
                          let uu____73047 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____73047
                          then
                            let uu____73052 =
                              let uu____73058 =
                                let uu____73060 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____73060
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____73058)
                               in
                            FStar_Errors.raise_error uu____73052
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____73066 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____73093  ->
                            match uu____73093 with
                            | (x,uu____73103,uu____73104) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____73066)))
            | uu____73162 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_73202 =
            match uu___449_73202 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____73226 = typars_of_binders _env binders  in
                (match uu____73226 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____73262 =
                         let uu____73263 =
                           let uu____73264 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____73264  in
                         FStar_Parser_AST.mk_term uu____73263
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____73262 binders  in
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
            | uu____73275 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____73318 =
              FStar_List.fold_left
                (fun uu____73352  ->
                   fun uu____73353  ->
                     match (uu____73352, uu____73353) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____73422 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____73422 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____73318 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____73513 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____73513
                | uu____73514 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____73522 = desugar_abstract_tc quals env [] tc  in
              (match uu____73522 with
               | (uu____73535,uu____73536,se,uu____73538) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____73541,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____73560 =
                                 let uu____73562 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____73562  in
                               if uu____73560
                               then
                                 let uu____73565 =
                                   let uu____73571 =
                                     let uu____73573 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____73573
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____73571)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____73565
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
                           | uu____73586 ->
                               let uu____73587 =
                                 let uu____73594 =
                                   let uu____73595 =
                                     let uu____73610 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____73610)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____73595
                                    in
                                 FStar_Syntax_Syntax.mk uu____73594  in
                               uu____73587 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_73623 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_73623.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_73623.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_73623.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____73624 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____73628 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____73628
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____73641 = typars_of_binders env binders  in
              (match uu____73641 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____73675 =
                           FStar_Util.for_some
                             (fun uu___450_73678  ->
                                match uu___450_73678 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____73681 -> false) quals
                            in
                         if uu____73675
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____73689 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____73689
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____73694 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_73700  ->
                               match uu___451_73700 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____73703 -> false))
                        in
                     if uu____73694
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____73717 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____73717
                     then
                       let uu____73723 =
                         let uu____73730 =
                           let uu____73731 = unparen t  in
                           uu____73731.FStar_Parser_AST.tm  in
                         match uu____73730 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73752 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73782)::args_rev ->
                                   let uu____73794 =
                                     let uu____73795 = unparen last_arg  in
                                     uu____73795.FStar_Parser_AST.tm  in
                                   (match uu____73794 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73823 -> ([], args))
                               | uu____73832 -> ([], args)  in
                             (match uu____73752 with
                              | (cattributes,args1) ->
                                  let uu____73871 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73871))
                         | uu____73882 -> (t, [])  in
                       match uu____73723 with
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
                                  (fun uu___452_73905  ->
                                     match uu___452_73905 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73908 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73917)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73941 = tycon_record_as_variant trec  in
              (match uu____73941 with
               | (t,fs) ->
                   let uu____73958 =
                     let uu____73961 =
                       let uu____73962 =
                         let uu____73971 =
                           let uu____73974 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73974  in
                         (uu____73971, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73962  in
                     uu____73961 :: quals  in
                   desugar_tycon env d uu____73958 [t])
          | uu____73979::uu____73980 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____74150 = et  in
                match uu____74150 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____74380 ->
                         let trec = tc  in
                         let uu____74404 = tycon_record_as_variant trec  in
                         (match uu____74404 with
                          | (t,fs) ->
                              let uu____74464 =
                                let uu____74467 =
                                  let uu____74468 =
                                    let uu____74477 =
                                      let uu____74480 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____74480  in
                                    (uu____74477, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____74468
                                   in
                                uu____74467 :: quals1  in
                              collect_tcs uu____74464 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____74570 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74570 with
                          | (env2,uu____74631,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74784 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74784 with
                          | (env2,uu____74845,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74973 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____75023 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____75023 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_75538  ->
                             match uu___454_75538 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____75604,uu____75605);
                                    FStar_Syntax_Syntax.sigrng = uu____75606;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____75607;
                                    FStar_Syntax_Syntax.sigmeta = uu____75608;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75609;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____75673 =
                                     typars_of_binders env1 binders  in
                                   match uu____75673 with
                                   | (env2,tpars1) ->
                                       let uu____75700 =
                                         push_tparams env2 tpars1  in
                                       (match uu____75700 with
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
                                 let uu____75729 =
                                   let uu____75748 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75748)
                                    in
                                 [uu____75729]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75808);
                                    FStar_Syntax_Syntax.sigrng = uu____75809;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75811;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75812;_},constrs,tconstr,quals1)
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
                                 let uu____75913 = push_tparams env1 tpars
                                    in
                                 (match uu____75913 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75980  ->
                                             match uu____75980 with
                                             | (x,uu____75992) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75997 =
                                        let uu____76024 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____76134  ->
                                                  match uu____76134 with
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
                                                        let uu____76194 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____76194
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
                                                                uu___453_76205
                                                                 ->
                                                                match uu___453_76205
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____76217
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____76225 =
                                                        let uu____76244 =
                                                          let uu____76245 =
                                                            let uu____76246 =
                                                              let uu____76262
                                                                =
                                                                let uu____76263
                                                                  =
                                                                  let uu____76266
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____76266
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____76263
                                                                 in
                                                              (name, univs1,
                                                                uu____76262,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____76246
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____76245;
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
                                                          uu____76244)
                                                         in
                                                      (name, uu____76225)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____76024
                                         in
                                      (match uu____75997 with
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
                             | uu____76478 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____76606  ->
                             match uu____76606 with
                             | (name_doc,uu____76632,uu____76633) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____76705  ->
                             match uu____76705 with
                             | (uu____76724,uu____76725,se) -> se))
                      in
                   let uu____76751 =
                     let uu____76758 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76758 rng
                      in
                   (match uu____76751 with
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
                               (fun uu____76820  ->
                                  match uu____76820 with
                                  | (uu____76841,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76889,tps,k,uu____76892,constrs)
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
                                      let uu____76913 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76928 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76945,uu____76946,uu____76947,uu____76948,uu____76949)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76956
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76928
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76960 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76967 
                                                          ->
                                                          match uu___455_76967
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76969 ->
                                                              true
                                                          | uu____76979 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76960))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76913
                                  | uu____76981 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76998  ->
                                 match uu____76998 with
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
      let uu____77043 =
        FStar_List.fold_left
          (fun uu____77078  ->
             fun b  ->
               match uu____77078 with
               | (env1,binders1) ->
                   let uu____77122 = desugar_binder env1 b  in
                   (match uu____77122 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____77145 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____77145 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____77198 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____77043 with
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
          let uu____77302 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_77309  ->
                    match uu___456_77309 with
                    | FStar_Syntax_Syntax.Reflectable uu____77311 -> true
                    | uu____77313 -> false))
             in
          if uu____77302
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____77318 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____77318
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
      let uu____77359 = FStar_Syntax_Util.head_and_args at1  in
      match uu____77359 with
      | (hd1,args) ->
          let uu____77412 =
            let uu____77427 =
              let uu____77428 = FStar_Syntax_Subst.compress hd1  in
              uu____77428.FStar_Syntax_Syntax.n  in
            (uu____77427, args)  in
          (match uu____77412 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____77453)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____77488 =
                 let uu____77493 =
                   let uu____77502 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____77502 a1  in
                 uu____77493 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____77488 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____77528 =
                      let uu____77537 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____77537, b)  in
                    FStar_Pervasives_Native.Some uu____77528
                | uu____77554 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____77608) when
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
           | uu____77643 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77815 = desugar_binders monad_env eff_binders  in
                  match uu____77815 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77855 =
                          let uu____77857 =
                            let uu____77866 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77866  in
                          FStar_List.length uu____77857  in
                        uu____77855 = (Prims.parse_int "1")  in
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
                            (uu____77950,uu____77951,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77953,uu____77954,uu____77955),uu____77956)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77993 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77996 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____78008 = name_of_eff_decl decl  in
                             FStar_List.mem uu____78008 mandatory_members)
                          eff_decls
                         in
                      (match uu____77996 with
                       | (mandatory_members_decls,actions) ->
                           let uu____78027 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____78056  ->
                                     fun decl  ->
                                       match uu____78056 with
                                       | (env2,out) ->
                                           let uu____78076 =
                                             desugar_decl env2 decl  in
                                           (match uu____78076 with
                                            | (env3,ses) ->
                                                let uu____78089 =
                                                  let uu____78092 =
                                                    FStar_List.hd ses  in
                                                  uu____78092 :: out  in
                                                (env3, uu____78089)))
                                  (env1, []))
                              in
                           (match uu____78027 with
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
                                              (uu____78161,uu____78162,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____78165,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____78166,(def,uu____78168)::
                                                      (cps_type,uu____78170)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____78171;
                                                   FStar_Parser_AST.level =
                                                     uu____78172;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____78228 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____78228 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____78266 =
                                                     let uu____78267 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____78268 =
                                                       let uu____78269 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____78269
                                                        in
                                                     let uu____78276 =
                                                       let uu____78277 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____78277
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____78267;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____78268;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____78276
                                                     }  in
                                                   (uu____78266, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____78286,uu____78287,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____78290,defn),doc1)::[])
                                              when for_free ->
                                              let uu____78329 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____78329 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____78367 =
                                                     let uu____78368 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____78369 =
                                                       let uu____78370 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____78370
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____78368;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____78369;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____78367, doc1))
                                          | uu____78379 ->
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
                                    let uu____78415 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____78415
                                     in
                                  let uu____78417 =
                                    let uu____78418 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____78418
                                     in
                                  ([], uu____78417)  in
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
                                      let uu____78436 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____78436)  in
                                    let uu____78443 =
                                      let uu____78444 =
                                        let uu____78445 =
                                          let uu____78446 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78446
                                           in
                                        let uu____78456 = lookup1 "return"
                                           in
                                        let uu____78458 = lookup1 "bind"  in
                                        let uu____78460 =
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
                                            uu____78445;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____78456;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____78458;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____78460
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____78444
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____78443;
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
                                         (fun uu___457_78468  ->
                                            match uu___457_78468 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____78471 -> true
                                            | uu____78473 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____78488 =
                                       let uu____78489 =
                                         let uu____78490 =
                                           lookup1 "return_wp"  in
                                         let uu____78492 = lookup1 "bind_wp"
                                            in
                                         let uu____78494 =
                                           lookup1 "if_then_else"  in
                                         let uu____78496 = lookup1 "ite_wp"
                                            in
                                         let uu____78498 = lookup1 "stronger"
                                            in
                                         let uu____78500 = lookup1 "close_wp"
                                            in
                                         let uu____78502 = lookup1 "assert_p"
                                            in
                                         let uu____78504 = lookup1 "assume_p"
                                            in
                                         let uu____78506 = lookup1 "null_wp"
                                            in
                                         let uu____78508 = lookup1 "trivial"
                                            in
                                         let uu____78510 =
                                           if rr
                                           then
                                             let uu____78512 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____78512
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____78530 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____78535 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____78540 =
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
                                             uu____78490;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____78492;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____78494;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____78496;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____78498;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____78500;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____78502;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____78504;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____78506;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____78508;
                                           FStar_Syntax_Syntax.repr =
                                             uu____78510;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____78530;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____78535;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____78540
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____78489
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____78488;
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
                                          fun uu____78566  ->
                                            match uu____78566 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____78580 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____78580
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
                let uu____78604 = desugar_binders env1 eff_binders  in
                match uu____78604 with
                | (env2,binders) ->
                    let uu____78641 =
                      let uu____78652 = head_and_args defn  in
                      match uu____78652 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____78689 ->
                                let uu____78690 =
                                  let uu____78696 =
                                    let uu____78698 =
                                      let uu____78700 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____78700 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____78698  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____78696)
                                   in
                                FStar_Errors.raise_error uu____78690
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____78706 =
                            match FStar_List.rev args with
                            | (last_arg,uu____78736)::args_rev ->
                                let uu____78748 =
                                  let uu____78749 = unparen last_arg  in
                                  uu____78749.FStar_Parser_AST.tm  in
                                (match uu____78748 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78777 -> ([], args))
                            | uu____78786 -> ([], args)  in
                          (match uu____78706 with
                           | (cattributes,args1) ->
                               let uu____78829 = desugar_args env2 args1  in
                               let uu____78830 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78829, uu____78830))
                       in
                    (match uu____78641 with
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
                          (let uu____78870 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78870 with
                           | (ed_binders,uu____78884,ed_binders_opening) ->
                               let sub' shift_n uu____78903 =
                                 match uu____78903 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78918 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78918 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78922 =
                                       let uu____78923 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78923)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78922
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78944 =
                                   let uu____78945 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78945
                                    in
                                 let uu____78960 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78961 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78962 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78963 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78964 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78965 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78966 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78967 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78968 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78969 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78970 =
                                   let uu____78971 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78971
                                    in
                                 let uu____78986 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78987 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78988 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____79004 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____79005 =
                                          let uu____79006 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____79006
                                           in
                                        let uu____79021 =
                                          let uu____79022 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____79022
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____79004;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____79005;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____79021
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
                                     uu____78944;
                                   FStar_Syntax_Syntax.ret_wp = uu____78960;
                                   FStar_Syntax_Syntax.bind_wp = uu____78961;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78962;
                                   FStar_Syntax_Syntax.ite_wp = uu____78963;
                                   FStar_Syntax_Syntax.stronger = uu____78964;
                                   FStar_Syntax_Syntax.close_wp = uu____78965;
                                   FStar_Syntax_Syntax.assert_p = uu____78966;
                                   FStar_Syntax_Syntax.assume_p = uu____78967;
                                   FStar_Syntax_Syntax.null_wp = uu____78968;
                                   FStar_Syntax_Syntax.trivial = uu____78969;
                                   FStar_Syntax_Syntax.repr = uu____78970;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78986;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78987;
                                   FStar_Syntax_Syntax.actions = uu____78988;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____79040 =
                                     let uu____79042 =
                                       let uu____79051 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____79051
                                        in
                                     FStar_List.length uu____79042  in
                                   uu____79040 = (Prims.parse_int "1")  in
                                 let uu____79084 =
                                   let uu____79087 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____79087 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____79084;
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
                                             let uu____79111 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____79111
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____79113 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____79113
                                 then
                                   let reflect_lid =
                                     let uu____79120 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____79120
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
    let uu____79132 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____79132 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____79217 ->
              let uu____79220 =
                let uu____79222 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____79222
                 in
              Prims.op_Hat "\n  " uu____79220
          | uu____79225 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____79244  ->
               match uu____79244 with
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
          let uu____79289 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____79289
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____79292 =
          let uu____79303 = FStar_Syntax_Syntax.as_arg arg  in [uu____79303]
           in
        FStar_Syntax_Util.mk_app fv uu____79292

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____79334 = desugar_decl_noattrs env d  in
      match uu____79334 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____79352 = mk_comment_attr d  in uu____79352 :: attrs1  in
          let uu____79353 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_79363 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_79363.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_79363.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_79363.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_79363.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_79366 = sigelt  in
                      let uu____79367 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____79373 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____79373) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_79366.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_79366.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_79366.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_79366.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____79367
                      })) sigelts
             in
          (env1, uu____79353)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____79399 = desugar_decl_aux env d  in
      match uu____79399 with
      | (env1,ses) ->
          let uu____79410 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____79410)

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
      | FStar_Parser_AST.Fsdoc uu____79438 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____79443 = FStar_Syntax_DsEnv.iface env  in
          if uu____79443
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____79458 =
               let uu____79460 =
                 let uu____79462 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____79463 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____79462
                   uu____79463
                  in
               Prims.op_Negation uu____79460  in
             if uu____79458
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____79477 =
                  let uu____79479 =
                    let uu____79481 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____79481 lid  in
                  Prims.op_Negation uu____79479  in
                if uu____79477
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____79495 =
                     let uu____79497 =
                       let uu____79499 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____79499
                         lid
                        in
                     Prims.op_Negation uu____79497  in
                   if uu____79495
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____79517 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____79517, [])
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
              | (FStar_Parser_AST.TyconRecord uu____79558,uu____79559)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____79598 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____79625  ->
                 match uu____79625 with | (x,uu____79633) -> x) tcs
             in
          let uu____79638 =
            let uu____79643 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____79643 tcs1  in
          (match uu____79638 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____79660 =
                   let uu____79661 =
                     let uu____79668 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____79668  in
                   [uu____79661]  in
                 let uu____79681 =
                   let uu____79684 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____79687 =
                     let uu____79698 =
                       let uu____79707 =
                         let uu____79708 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____79708  in
                       FStar_Syntax_Syntax.as_arg uu____79707  in
                     [uu____79698]  in
                   FStar_Syntax_Util.mk_app uu____79684 uu____79687  in
                 FStar_Syntax_Util.abs uu____79660 uu____79681
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79748,id1))::uu____79750 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79753::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79757 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79757 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79763 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79763]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79784) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79794,uu____79795,uu____79796,uu____79797,uu____79798)
                     ->
                     let uu____79807 =
                       let uu____79808 =
                         let uu____79809 =
                           let uu____79816 = mkclass lid  in
                           (meths, uu____79816)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79809  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79808;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79807]
                 | uu____79819 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79853;
                    FStar_Parser_AST.prange = uu____79854;_},uu____79855)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79865;
                    FStar_Parser_AST.prange = uu____79866;_},uu____79867)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79883;
                         FStar_Parser_AST.prange = uu____79884;_},uu____79885);
                    FStar_Parser_AST.prange = uu____79886;_},uu____79887)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79909;
                         FStar_Parser_AST.prange = uu____79910;_},uu____79911);
                    FStar_Parser_AST.prange = uu____79912;_},uu____79913)::[]
                   -> false
               | (p,uu____79942)::[] ->
                   let uu____79951 = is_app_pattern p  in
                   Prims.op_Negation uu____79951
               | uu____79953 -> false)
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
            let uu____80028 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____80028 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____80041 =
                     let uu____80042 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____80042.FStar_Syntax_Syntax.n  in
                   match uu____80041 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____80052) ->
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
                         | uu____80088::uu____80089 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____80092 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_80108  ->
                                     match uu___458_80108 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____80111;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____80112;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____80113;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____80114;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____80115;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____80116;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____80117;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____80129;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____80130;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____80131;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____80132;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____80133;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____80134;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____80148 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____80181  ->
                                   match uu____80181 with
                                   | (uu____80195,(uu____80196,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____80148
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____80216 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____80216
                         then
                           let uu____80222 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_80237 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_80239 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_80239.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_80239.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_80237.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____80222)
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
                   | uu____80269 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____80277 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____80296 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____80277 with
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
                       let uu___4019_80333 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_80333.FStar_Parser_AST.prange)
                       }
                   | uu____80340 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_80347 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_80347.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_80347.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_80347.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____80383 id1 =
                   match uu____80383 with
                   | (env1,ses) ->
                       let main =
                         let uu____80404 =
                           let uu____80405 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____80405  in
                         FStar_Parser_AST.mk_term uu____80404
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
                       let uu____80455 = desugar_decl env1 id_decl  in
                       (match uu____80455 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____80473 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____80473 FStar_Util.set_elements
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
            let uu____80497 = close_fun env t  in
            desugar_term env uu____80497  in
          let quals1 =
            let uu____80501 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____80501
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____80513 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____80513;
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
                let uu____80527 =
                  let uu____80536 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____80536]  in
                let uu____80555 =
                  let uu____80558 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____80558
                   in
                FStar_Syntax_Util.arrow uu____80527 uu____80555
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
            let uu____80613 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____80613 with
            | FStar_Pervasives_Native.None  ->
                let uu____80616 =
                  let uu____80622 =
                    let uu____80624 =
                      let uu____80626 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____80626 " not found"  in
                    Prims.op_Hat "Effect name " uu____80624  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____80622)  in
                FStar_Errors.raise_error uu____80616
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____80634 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____80652 =
                  let uu____80655 =
                    let uu____80656 = desugar_term env t  in
                    ([], uu____80656)  in
                  FStar_Pervasives_Native.Some uu____80655  in
                (uu____80652, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____80669 =
                  let uu____80672 =
                    let uu____80673 = desugar_term env wp  in
                    ([], uu____80673)  in
                  FStar_Pervasives_Native.Some uu____80672  in
                let uu____80680 =
                  let uu____80683 =
                    let uu____80684 = desugar_term env t  in
                    ([], uu____80684)  in
                  FStar_Pervasives_Native.Some uu____80683  in
                (uu____80669, uu____80680)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____80696 =
                  let uu____80699 =
                    let uu____80700 = desugar_term env t  in
                    ([], uu____80700)  in
                  FStar_Pervasives_Native.Some uu____80699  in
                (FStar_Pervasives_Native.None, uu____80696)
             in
          (match uu____80634 with
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
            let uu____80734 =
              let uu____80735 =
                let uu____80742 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80742, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____80735  in
            {
              FStar_Syntax_Syntax.sigel = uu____80734;
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
      let uu____80769 =
        FStar_List.fold_left
          (fun uu____80789  ->
             fun d  ->
               match uu____80789 with
               | (env1,sigelts) ->
                   let uu____80809 = desugar_decl env1 d  in
                   (match uu____80809 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80769 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80854 =
            match uu___460_80854 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80868,FStar_Syntax_Syntax.Sig_let uu____80869) ->
                     let uu____80882 =
                       let uu____80885 =
                         let uu___4152_80886 = se2  in
                         let uu____80887 =
                           let uu____80890 =
                             FStar_List.filter
                               (fun uu___459_80904  ->
                                  match uu___459_80904 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80909;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80910;_},uu____80911);
                                      FStar_Syntax_Syntax.pos = uu____80912;
                                      FStar_Syntax_Syntax.vars = uu____80913;_}
                                      when
                                      let uu____80940 =
                                        let uu____80942 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80942
                                         in
                                      uu____80940 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80946 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80890
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80886.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80886.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80886.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80886.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80887
                         }  in
                       uu____80885 :: se1 :: acc  in
                     forward uu____80882 sigelts1
                 | uu____80952 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80960 = forward [] sigelts  in (env1, uu____80960)
  
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
          | (FStar_Pervasives_Native.None ,uu____81025) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____81029;
               FStar_Syntax_Syntax.exports = uu____81030;
               FStar_Syntax_Syntax.is_interface = uu____81031;_},FStar_Parser_AST.Module
             (current_lid,uu____81033)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____81042) ->
              let uu____81045 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____81045
           in
        let uu____81050 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____81092 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____81092, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____81114 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____81114, mname, decls, false)
           in
        match uu____81050 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____81156 = desugar_decls env2 decls  in
            (match uu____81156 with
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
          let uu____81224 =
            (FStar_Options.interactive ()) &&
              (let uu____81227 =
                 let uu____81229 =
                   let uu____81231 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____81231  in
                 FStar_Util.get_file_extension uu____81229  in
               FStar_List.mem uu____81227 ["fsti"; "fsi"])
             in
          if uu____81224 then as_interface m else m  in
        let uu____81245 = desugar_modul_common curmod env m1  in
        match uu____81245 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____81267 = FStar_Syntax_DsEnv.pop ()  in
              (uu____81267, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____81289 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____81289 with
      | (env1,modul,pop_when_done) ->
          let uu____81306 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____81306 with
           | (env2,modul1) ->
               ((let uu____81318 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____81318
                 then
                   let uu____81321 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____81321
                 else ());
                (let uu____81326 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____81326, modul1))))
  
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
        (fun uu____81376  ->
           let uu____81377 = desugar_modul env modul  in
           match uu____81377 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____81415  ->
           let uu____81416 = desugar_decls env decls  in
           match uu____81416 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____81467  ->
             let uu____81468 = desugar_partial_modul modul env a_modul  in
             match uu____81468 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____81563 ->
                  let t =
                    let uu____81573 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____81573  in
                  let uu____81586 =
                    let uu____81587 = FStar_Syntax_Subst.compress t  in
                    uu____81587.FStar_Syntax_Syntax.n  in
                  (match uu____81586 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____81599,uu____81600)
                       -> bs1
                   | uu____81625 -> failwith "Impossible")
               in
            let uu____81635 =
              let uu____81642 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____81642
                FStar_Syntax_Syntax.t_unit
               in
            match uu____81635 with
            | (binders,uu____81644,binders_opening) ->
                let erase_term t =
                  let uu____81652 =
                    let uu____81653 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____81653  in
                  FStar_Syntax_Subst.close binders uu____81652  in
                let erase_tscheme uu____81671 =
                  match uu____81671 with
                  | (us,t) ->
                      let t1 =
                        let uu____81691 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____81691 t  in
                      let uu____81694 =
                        let uu____81695 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____81695  in
                      ([], uu____81694)
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
                    | uu____81718 ->
                        let bs =
                          let uu____81728 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____81728  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81768 =
                          let uu____81769 =
                            let uu____81772 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81772  in
                          uu____81769.FStar_Syntax_Syntax.n  in
                        (match uu____81768 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81774,uu____81775) -> bs1
                         | uu____81800 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81808 =
                      let uu____81809 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81809  in
                    FStar_Syntax_Subst.close binders uu____81808  in
                  let uu___4311_81810 = action  in
                  let uu____81811 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81812 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81810.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81810.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81811;
                    FStar_Syntax_Syntax.action_typ = uu____81812
                  }  in
                let uu___4313_81813 = ed  in
                let uu____81814 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81815 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81816 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81817 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81818 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81819 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81820 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81821 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81822 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81823 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81824 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81825 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81826 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81827 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81828 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81829 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81813.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81813.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81814;
                  FStar_Syntax_Syntax.signature = uu____81815;
                  FStar_Syntax_Syntax.ret_wp = uu____81816;
                  FStar_Syntax_Syntax.bind_wp = uu____81817;
                  FStar_Syntax_Syntax.if_then_else = uu____81818;
                  FStar_Syntax_Syntax.ite_wp = uu____81819;
                  FStar_Syntax_Syntax.stronger = uu____81820;
                  FStar_Syntax_Syntax.close_wp = uu____81821;
                  FStar_Syntax_Syntax.assert_p = uu____81822;
                  FStar_Syntax_Syntax.assume_p = uu____81823;
                  FStar_Syntax_Syntax.null_wp = uu____81824;
                  FStar_Syntax_Syntax.trivial = uu____81825;
                  FStar_Syntax_Syntax.repr = uu____81826;
                  FStar_Syntax_Syntax.return_repr = uu____81827;
                  FStar_Syntax_Syntax.bind_repr = uu____81828;
                  FStar_Syntax_Syntax.actions = uu____81829;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81813.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81845 = se  in
                  let uu____81846 =
                    let uu____81847 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81847  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81846;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81845.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81845.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81845.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81845.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81851 = se  in
                  let uu____81852 =
                    let uu____81853 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81853
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81852;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81851.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81851.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81851.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81851.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81855 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81856 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81856 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81873 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81873
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81875 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81875)
  