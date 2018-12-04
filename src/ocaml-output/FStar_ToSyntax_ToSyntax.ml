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
             (fun uu____104  ->
                match uu____104 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____159  ->
                             match uu____159 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____177 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____177 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____183 =
                                     let uu____184 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____184]  in
                                   FStar_Syntax_Subst.close uu____183 branch1
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
      fun uu___247_241  ->
        match uu___247_241 with
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
  fun uu___248_261  ->
    match uu___248_261 with
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
  fun uu___249_279  ->
    match uu___249_279 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____282 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____290 .
    FStar_Parser_AST.imp ->
      'Auu____290 ->
        ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____316 .
    FStar_Parser_AST.imp ->
      'Auu____316 ->
        ('Auu____316 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____335 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____356 -> true
            | uu____362 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____371 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____378 =
      let uu____379 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____379  in
    FStar_Parser_AST.mk_term uu____378 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____389 =
      let uu____390 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____390  in
    FStar_Parser_AST.mk_term uu____389 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____406 =
        let uu____407 = unparen t  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.Name l ->
          let uu____410 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____410 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____417) ->
          let uu____430 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____430 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____437,uu____438) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____443,uu____444) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____449,t1) -> is_comp_type env t1
      | uu____451 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____474 =
          let uu____477 =
            let uu____478 =
              let uu____484 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____484, r)  in
            FStar_Ident.mk_ident uu____478  in
          [uu____477]  in
        FStar_All.pipe_right uu____474 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____500 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____500 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____538 =
              let uu____539 =
                let uu____540 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____540 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____539 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____538  in
          let fallback uu____548 =
            let uu____549 = FStar_Ident.text_of_id op  in
            match uu____549 with
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
                let uu____570 = FStar_Options.ml_ish ()  in
                if uu____570
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.delta_equational
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
            | uu____596 -> FStar_Pervasives_Native.None  in
          let uu____598 =
            let uu____601 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____601  in
          match uu____598 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____605 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____620 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____620
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____669 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____673 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____673 with | (env1,uu____685) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____688,term) ->
          let uu____690 = free_type_vars env term  in (env, uu____690)
      | FStar_Parser_AST.TAnnotated (id1,uu____696) ->
          let uu____697 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____697 with | (env1,uu____709) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____713 = free_type_vars env t  in (env, uu____713)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____720 =
        let uu____721 = unparen t  in uu____721.FStar_Parser_AST.tm  in
      match uu____720 with
      | FStar_Parser_AST.Labeled uu____724 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____737 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____737 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____742 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____745 -> []
      | FStar_Parser_AST.Uvar uu____746 -> []
      | FStar_Parser_AST.Var uu____747 -> []
      | FStar_Parser_AST.Projector uu____748 -> []
      | FStar_Parser_AST.Discrim uu____753 -> []
      | FStar_Parser_AST.Name uu____754 -> []
      | FStar_Parser_AST.Requires (t1,uu____756) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____764) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____771,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____790,ts) ->
          FStar_List.collect
            (fun uu____811  ->
               match uu____811 with | (t1,uu____819) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____820,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____828) ->
          let uu____829 = free_type_vars env t1  in
          let uu____832 = free_type_vars env t2  in
          FStar_List.append uu____829 uu____832
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____837 = free_type_vars_b env b  in
          (match uu____837 with
           | (env1,f) ->
               let uu____852 = free_type_vars env1 t1  in
               FStar_List.append f uu____852)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____869 =
            FStar_List.fold_left
              (fun uu____893  ->
                 fun bt  ->
                   match uu____893 with
                   | (env1,free) ->
                       let uu____917 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____932 = free_type_vars env1 body  in
                             (env1, uu____932)
                          in
                       (match uu____917 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____869 with
           | (env1,free) ->
               let uu____961 = free_type_vars env1 body  in
               FStar_List.append free uu____961)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____970 =
            FStar_List.fold_left
              (fun uu____990  ->
                 fun binder  ->
                   match uu____990 with
                   | (env1,free) ->
                       let uu____1010 = free_type_vars_b env1 binder  in
                       (match uu____1010 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____970 with
           | (env1,free) ->
               let uu____1041 = free_type_vars env1 body  in
               FStar_List.append free uu____1041)
      | FStar_Parser_AST.Project (t1,uu____1045) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1056 = free_type_vars env rel  in
          let uu____1059 =
            let uu____1062 = free_type_vars env init1  in
            let uu____1065 =
              FStar_List.collect
                (fun uu____1074  ->
                   match uu____1074 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1080 = free_type_vars env rel1  in
                       let uu____1083 =
                         let uu____1086 = free_type_vars env just  in
                         let uu____1089 = free_type_vars env next  in
                         FStar_List.append uu____1086 uu____1089  in
                       FStar_List.append uu____1080 uu____1083) steps
               in
            FStar_List.append uu____1062 uu____1065  in
          FStar_List.append uu____1056 uu____1059
      | FStar_Parser_AST.Abs uu____1092 -> []
      | FStar_Parser_AST.Let uu____1099 -> []
      | FStar_Parser_AST.LetOpen uu____1120 -> []
      | FStar_Parser_AST.If uu____1125 -> []
      | FStar_Parser_AST.QForall uu____1132 -> []
      | FStar_Parser_AST.QExists uu____1145 -> []
      | FStar_Parser_AST.Record uu____1158 -> []
      | FStar_Parser_AST.Match uu____1171 -> []
      | FStar_Parser_AST.TryWith uu____1186 -> []
      | FStar_Parser_AST.Bind uu____1201 -> []
      | FStar_Parser_AST.Quote uu____1208 -> []
      | FStar_Parser_AST.VQuote uu____1213 -> []
      | FStar_Parser_AST.Antiquote uu____1214 -> []
      | FStar_Parser_AST.Seq uu____1215 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1269 =
        let uu____1270 = unparen t1  in uu____1270.FStar_Parser_AST.tm  in
      match uu____1269 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1312 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1337 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1337  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1359 =
                     let uu____1360 =
                       let uu____1365 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1365)  in
                     FStar_Parser_AST.TAnnotated uu____1360  in
                   FStar_Parser_AST.mk_binder uu____1359
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
        let uu____1383 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1383  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1405 =
                     let uu____1406 =
                       let uu____1411 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1411)  in
                     FStar_Parser_AST.TAnnotated uu____1406  in
                   FStar_Parser_AST.mk_binder uu____1405
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1413 =
             let uu____1414 = unparen t  in uu____1414.FStar_Parser_AST.tm
              in
           match uu____1413 with
           | FStar_Parser_AST.Product uu____1415 -> t
           | uu____1422 ->
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
      | uu____1459 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1470 -> true
    | FStar_Parser_AST.PatTvar (uu____1474,uu____1475) -> true
    | FStar_Parser_AST.PatVar (uu____1481,uu____1482) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1489) -> is_var_pattern p1
    | uu____1502 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1513) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1526;
           FStar_Parser_AST.prange = uu____1527;_},uu____1528)
        -> true
    | uu____1540 -> false
  
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
    | uu____1556 -> p
  
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
            let uu____1629 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1629 with
             | (name,args,uu____1672) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1722);
               FStar_Parser_AST.prange = uu____1723;_},args)
            when is_top_level1 ->
            let uu____1733 =
              let uu____1738 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1738  in
            (uu____1733, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1760);
               FStar_Parser_AST.prange = uu____1761;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1791 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____1850 -> acc
        | FStar_Parser_AST.PatName uu____1853 -> acc
        | FStar_Parser_AST.PatOp uu____1854 -> acc
        | FStar_Parser_AST.PatConst uu____1855 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1872) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1878) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1887) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1904 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1904
        | FStar_Parser_AST.PatAscribed (pat,uu____1912) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1994 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2036 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___250_2085  ->
    match uu___250_2085 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2092 -> failwith "Impossible"
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2127  ->
    match uu____2127 with
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
      let uu____2209 =
        let uu____2226 =
          let uu____2229 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2229  in
        let uu____2230 =
          let uu____2241 =
            let uu____2250 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2250)  in
          [uu____2241]  in
        (uu____2226, uu____2230)  in
      FStar_Syntax_Syntax.Tm_app uu____2209  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2299 =
        let uu____2316 =
          let uu____2319 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2319  in
        let uu____2320 =
          let uu____2331 =
            let uu____2340 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2340)  in
          [uu____2331]  in
        (uu____2316, uu____2320)  in
      FStar_Syntax_Syntax.Tm_app uu____2299  in
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
          let uu____2403 =
            let uu____2420 =
              let uu____2423 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2423  in
            let uu____2424 =
              let uu____2435 =
                let uu____2444 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2444)  in
              let uu____2452 =
                let uu____2463 =
                  let uu____2472 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2472)  in
                [uu____2463]  in
              uu____2435 :: uu____2452  in
            (uu____2420, uu____2424)  in
          FStar_Syntax_Syntax.Tm_app uu____2403  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2532 =
        let uu____2547 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2566  ->
               match uu____2566 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2577;
                    FStar_Syntax_Syntax.index = uu____2578;
                    FStar_Syntax_Syntax.sort = t;_},uu____2580)
                   ->
                   let uu____2588 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2588) uu____2547
         in
      FStar_All.pipe_right bs uu____2532  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2604 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2622 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2650 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2671,uu____2672,bs,t,uu____2675,uu____2676)
                            ->
                            let uu____2685 = bs_univnames bs  in
                            let uu____2688 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2685 uu____2688
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2691,uu____2692,t,uu____2694,uu____2695,uu____2696)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2703 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2650 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___278_2712 = s  in
        let uu____2713 =
          let uu____2714 =
            let uu____2723 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2741,bs,t,lids1,lids2) ->
                          let uu___279_2754 = se  in
                          let uu____2755 =
                            let uu____2756 =
                              let uu____2773 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2774 =
                                let uu____2775 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2775 t  in
                              (lid, uvs, uu____2773, uu____2774, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2756
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2755;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___279_2754.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___279_2754.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___279_2754.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___279_2754.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2789,t,tlid,n1,lids1) ->
                          let uu___280_2800 = se  in
                          let uu____2801 =
                            let uu____2802 =
                              let uu____2818 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2818, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2802  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2801;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___280_2800.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___280_2800.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___280_2800.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___280_2800.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2822 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2723, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2714  in
        {
          FStar_Syntax_Syntax.sigel = uu____2713;
          FStar_Syntax_Syntax.sigrng =
            (uu___278_2712.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___278_2712.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___278_2712.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___278_2712.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2829,t) ->
        let uvs =
          let uu____2832 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2832 FStar_Util.set_elements  in
        let uu___281_2837 = s  in
        let uu____2838 =
          let uu____2839 =
            let uu____2846 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2846)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2839  in
        {
          FStar_Syntax_Syntax.sigel = uu____2838;
          FStar_Syntax_Syntax.sigrng =
            (uu___281_2837.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___281_2837.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___281_2837.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___281_2837.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2870 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2873 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2880) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2913,(FStar_Util.Inl t,uu____2915),uu____2916)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2963,(FStar_Util.Inr c,uu____2965),uu____2966)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3013 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3014,(FStar_Util.Inl t,uu____3016),uu____3017) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3064,(FStar_Util.Inr c,uu____3066),uu____3067) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3114 -> empty_set  in
          FStar_Util.set_union uu____2870 uu____2873  in
        let all_lb_univs =
          let uu____3118 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3134 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3134) empty_set)
             in
          FStar_All.pipe_right uu____3118 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___282_3144 = s  in
        let uu____3145 =
          let uu____3146 =
            let uu____3153 =
              let uu____3154 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___283_3166 = lb  in
                        let uu____3167 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3170 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___283_3166.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3167;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___283_3166.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3170;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___283_3166.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___283_3166.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3154)  in
            (uu____3153, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3146  in
        {
          FStar_Syntax_Syntax.sigel = uu____3145;
          FStar_Syntax_Syntax.sigrng =
            (uu___282_3144.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___282_3144.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___282_3144.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___282_3144.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3179,fml) ->
        let uvs =
          let uu____3182 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3182 FStar_Util.set_elements  in
        let uu___284_3187 = s  in
        let uu____3188 =
          let uu____3189 =
            let uu____3196 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3196)  in
          FStar_Syntax_Syntax.Sig_assume uu____3189  in
        {
          FStar_Syntax_Syntax.sigel = uu____3188;
          FStar_Syntax_Syntax.sigrng =
            (uu___284_3187.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___284_3187.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___284_3187.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___284_3187.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3198,bs,c,flags1) ->
        let uvs =
          let uu____3207 =
            let uu____3210 = bs_univnames bs  in
            let uu____3213 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3210 uu____3213  in
          FStar_All.pipe_right uu____3207 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___285_3221 = s  in
        let uu____3222 =
          let uu____3223 =
            let uu____3236 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3237 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3236, uu____3237, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3223  in
        {
          FStar_Syntax_Syntax.sigel = uu____3222;
          FStar_Syntax_Syntax.sigrng =
            (uu___285_3221.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___285_3221.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___285_3221.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___285_3221.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3240 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___251_3248  ->
    match uu___251_3248 with
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
    | uu____3299 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3320 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3320)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3346 =
      let uu____3347 = unparen t  in uu____3347.FStar_Parser_AST.tm  in
    match uu____3346 with
    | FStar_Parser_AST.Wild  ->
        let uu____3353 =
          let uu____3354 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3354  in
        FStar_Util.Inr uu____3353
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3367)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.strcat
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
             let uu____3458 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3458
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3475 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3475
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3491 =
               let uu____3497 =
                 let uu____3499 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3499
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3497)
                in
             FStar_Errors.raise_error uu____3491 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3508 ->
        let rec aux t1 univargs =
          let uu____3545 =
            let uu____3546 = unparen t1  in uu____3546.FStar_Parser_AST.tm
             in
          match uu____3545 with
          | FStar_Parser_AST.App (t2,targ,uu____3554) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___252_3581  ->
                     match uu___252_3581 with
                     | FStar_Util.Inr uu____3588 -> true
                     | uu____3591 -> false) univargs
              then
                let uu____3599 =
                  let uu____3600 =
                    FStar_List.map
                      (fun uu___253_3610  ->
                         match uu___253_3610 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3600  in
                FStar_Util.Inr uu____3599
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___254_3636  ->
                        match uu___254_3636 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3646 -> failwith "impossible")
                     univargs
                    in
                 let uu____3650 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3650)
          | uu____3666 ->
              let uu____3667 =
                let uu____3673 =
                  let uu____3675 =
                    let uu____3677 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3677 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3675  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3673)  in
              FStar_Errors.raise_error uu____3667 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3692 ->
        let uu____3693 =
          let uu____3699 =
            let uu____3701 =
              let uu____3703 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3703 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3701  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3699)  in
        FStar_Errors.raise_error uu____3693 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3744;_});
            FStar_Syntax_Syntax.pos = uu____3745;
            FStar_Syntax_Syntax.vars = uu____3746;_})::uu____3747
        ->
        let uu____3778 =
          let uu____3784 =
            let uu____3786 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3786
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3784)  in
        FStar_Errors.raise_error uu____3778 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3792 ->
        let uu____3811 =
          let uu____3817 =
            let uu____3819 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3819
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3817)  in
        FStar_Errors.raise_error uu____3811 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3832 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____3832) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3860 = FStar_List.hd fields  in
        match uu____3860 with
        | (f,uu____3870) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3882 =
                match uu____3882 with
                | (f',uu____3888) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3890 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3890
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
              (let uu____3900 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3900);
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
                | (p2,uu____4356) ->
                    let intersection =
                      let uu____4366 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4366 out  in
                    let uu____4369 = FStar_Util.set_is_empty intersection  in
                    if uu____4369
                    then
                      let uu____4374 = pat_vars p2  in
                      FStar_Util.set_union out uu____4374
                    else
                      (let duplicate_bv =
                         let uu____4380 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4380  in
                       let uu____4383 =
                         let uu____4389 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
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
        | p1::[] ->
            let uu____4413 = pat_vars p1  in
            FStar_All.pipe_right uu____4413 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4441 =
                let uu____4443 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4443  in
              if uu____4441
              then ()
              else
                (let nonlinear_vars =
                   let uu____4452 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4452  in
                 let first_nonlinear_var =
                   let uu____4456 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4456  in
                 let uu____4459 =
                   let uu____4465 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4465)  in
                 FStar_Errors.raise_error uu____4459 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4493 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4493 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4510 ->
            let uu____4513 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4513 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4664 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4688 =
              let uu____4689 =
                let uu____4690 =
                  let uu____4697 =
                    let uu____4698 =
                      let uu____4704 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4704, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4698  in
                  (uu____4697, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4690  in
              {
                FStar_Parser_AST.pat = uu____4689;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4688
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4724 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4727 = aux loc env1 p2  in
              match uu____4727 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___286_4816 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___287_4821 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___287_4821.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___287_4821.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___286_4816.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___288_4823 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___289_4828 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___289_4828.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___289_4828.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___288_4823.FStar_Syntax_Syntax.p)
                        }
                    | uu____4829 when top -> p4
                    | uu____4830 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4835 =
                    match binder with
                    | LetBinder uu____4856 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4881 = close_fun env1 t  in
                          desugar_term env1 uu____4881  in
                        let x1 =
                          let uu___290_4883 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___290_4883.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___290_4883.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4835 with
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
            let uu____4951 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4951, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4965 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4965, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4989 = resolvex loc env1 x  in
            (match uu____4989 with
             | (loc1,env2,xbv) ->
                 let uu____5018 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5018, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5041 = resolvex loc env1 x  in
            (match uu____5041 with
             | (loc1,env2,xbv) ->
                 let uu____5070 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5070, [], imp))
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
            let uu____5085 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5085, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5115;_},args)
            ->
            let uu____5121 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5182  ->
                     match uu____5182 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5263 = aux loc1 env2 arg  in
                         (match uu____5263 with
                          | (loc2,env3,uu____5310,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5121 with
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
                 let uu____5442 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5442, annots, false))
        | FStar_Parser_AST.PatApp uu____5460 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5491 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5542  ->
                     match uu____5542 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5603 = aux loc1 env2 pat  in
                         (match uu____5603 with
                          | (loc2,env3,uu____5645,pat1,ans,uu____5648) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5491 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5745 =
                     let uu____5748 =
                       let uu____5755 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5755  in
                     let uu____5756 =
                       let uu____5757 =
                         let uu____5771 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5771, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5757  in
                     FStar_All.pipe_left uu____5748 uu____5756  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5805 =
                            let uu____5806 =
                              let uu____5820 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5820, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5806  in
                          FStar_All.pipe_left (pos_r r) uu____5805) pats1
                     uu____5745
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
            let uu____5878 =
              FStar_List.fold_left
                (fun uu____5938  ->
                   fun p2  ->
                     match uu____5938 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6020 = aux loc1 env2 p2  in
                         (match uu____6020 with
                          | (loc2,env3,uu____6067,pat,ans,uu____6070) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5878 with
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
                   | uu____6236 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6239 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6239, annots, false))
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
                   (fun uu____6320  ->
                      match uu____6320 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6350  ->
                      match uu____6350 with
                      | (f,uu____6356) ->
                          let uu____6357 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6383  ->
                                    match uu____6383 with
                                    | (g,uu____6390) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6357 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6396,p2) ->
                               p2)))
               in
            let app =
              let uu____6403 =
                let uu____6404 =
                  let uu____6411 =
                    let uu____6412 =
                      let uu____6413 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6413  in
                    FStar_Parser_AST.mk_pattern uu____6412
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6411, args)  in
                FStar_Parser_AST.PatApp uu____6404  in
              FStar_Parser_AST.mk_pattern uu____6403
                p1.FStar_Parser_AST.prange
               in
            let uu____6416 = aux loc env1 app  in
            (match uu____6416 with
             | (env2,e,b,p2,annots,uu____6462) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6502 =
                         let uu____6503 =
                           let uu____6517 =
                             let uu___291_6518 = fv  in
                             let uu____6519 =
                               let uu____6522 =
                                 let uu____6523 =
                                   let uu____6530 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6530)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6523
                                  in
                               FStar_Pervasives_Native.Some uu____6522  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___291_6518.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___291_6518.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6519
                             }  in
                           (uu____6517, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6503  in
                       FStar_All.pipe_left pos uu____6502
                   | uu____6556 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6642 = aux' true loc env1 p2  in
            (match uu____6642 with
             | (loc1,env2,var,p3,ans,uu____6686) ->
                 let uu____6701 =
                   FStar_List.fold_left
                     (fun uu____6750  ->
                        fun p4  ->
                          match uu____6750 with
                          | (loc2,env3,ps1) ->
                              let uu____6815 = aux' true loc2 env3 p4  in
                              (match uu____6815 with
                               | (loc3,env4,uu____6856,p5,ans1,uu____6859) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6701 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7020 ->
            let uu____7021 = aux' true loc env1 p1  in
            (match uu____7021 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7118 = aux_maybe_or env p  in
      match uu____7118 with
      | (env1,b,pats) ->
          ((let uu____7173 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7173
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
          let uu____7246 =
            let uu____7247 =
              let uu____7258 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7258, (ty, tacopt))  in
            LetBinder uu____7247  in
          (env, uu____7246, [])  in
        let op_to_ident x =
          let uu____7275 =
            let uu____7281 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7281, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7275  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7303 = op_to_ident x  in
              mklet uu____7303 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7305) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7311;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7327 = op_to_ident x  in
              let uu____7328 = desugar_term env t  in
              mklet uu____7327 uu____7328 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7330);
                 FStar_Parser_AST.prange = uu____7331;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7351 = desugar_term env t  in
              mklet x uu____7351 tacopt1
          | uu____7352 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7365 = desugar_data_pat env p  in
           match uu____7365 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7394;
                      FStar_Syntax_Syntax.p = uu____7395;_},uu____7396)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7409;
                      FStar_Syntax_Syntax.p = uu____7410;_},uu____7411)::[]
                     -> []
                 | uu____7424 -> p1  in
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
  fun uu____7432  ->
    fun env  ->
      fun pat  ->
        let uu____7436 = desugar_data_pat env pat  in
        match uu____7436 with | (env1,uu____7452,pat1) -> (env1, pat1)

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
      let uu____7474 = desugar_term_aq env e  in
      match uu____7474 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7493 = desugar_typ_aq env e  in
      match uu____7493 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7503  ->
        fun range  ->
          match uu____7503 with
          | (signedness,width) ->
              let tnm =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7525 =
                  let uu____7527 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7527  in
                if uu____7525
                then
                  let uu____7530 =
                    let uu____7536 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7536)  in
                  FStar_Errors.log_issue range uu____7530
                else ());
               (let private_intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat ".__"
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat "."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7557 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7557 range  in
                let lid1 =
                  let uu____7561 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7561 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7571 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7571 range  in
                           let private_fv =
                             let uu____7573 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7573 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___292_7574 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___292_7574.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___292_7574.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7575 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7579 =
                        let uu____7585 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7585)
                         in
                      FStar_Errors.raise_error uu____7579 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7605 =
                  let uu____7612 =
                    let uu____7613 =
                      let uu____7630 =
                        let uu____7641 =
                          let uu____7650 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7650)  in
                        [uu____7641]  in
                      (lid1, uu____7630)  in
                    FStar_Syntax_Syntax.Tm_app uu____7613  in
                  FStar_Syntax_Syntax.mk uu____7612  in
                uu____7605 FStar_Pervasives_Native.None range))

and (desugar_name :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____7701 =
              let uu____7708 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7708 l  in
            match uu____7701 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7760;
                              FStar_Syntax_Syntax.vars = uu____7761;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7789 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7789 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7805 =
                                 let uu____7806 =
                                   let uu____7809 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7809  in
                                 uu____7806.FStar_Syntax_Syntax.n  in
                               match uu____7805 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7832))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7839 -> msg
                             else msg  in
                           let uu____7842 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7842
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7847 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7847 " is deprecated"  in
                           let uu____7850 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7850
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7852 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7867 =
          let uu____7868 = unparen t  in uu____7868.FStar_Parser_AST.tm  in
        match uu____7867 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7869; FStar_Ident.ident = uu____7870;
              FStar_Ident.nsstr = uu____7871; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7876 ->
            let uu____7877 =
              let uu____7883 =
                let uu____7885 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7885  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7883)  in
            FStar_Errors.raise_error uu____7877 t.FStar_Parser_AST.range
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
          let uu___293_7972 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___293_7972.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___293_7972.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7975 =
          let uu____7976 = unparen top  in uu____7976.FStar_Parser_AST.tm  in
        match uu____7975 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7981 ->
            let uu____7990 = desugar_formula env top  in (uu____7990, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7999 = desugar_formula env t  in (uu____7999, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8008 = desugar_formula env t  in (uu____8008, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8035 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8035, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8037 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8037, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8046 =
                let uu____8047 =
                  let uu____8054 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8054, args)  in
                FStar_Parser_AST.Op uu____8047  in
              FStar_Parser_AST.mk_term uu____8046 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8059 =
              let uu____8060 =
                let uu____8061 =
                  let uu____8068 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8068, [e])  in
                FStar_Parser_AST.Op uu____8061  in
              FStar_Parser_AST.mk_term uu____8060 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8059
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8080 = FStar_Ident.text_of_id op_star  in
             uu____8080 = "*") &&
              (let uu____8085 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8085 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8102;_},t1::t2::[])
                  when
                  let uu____8108 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8108 FStar_Option.isNone ->
                  let uu____8115 = flatten1 t1  in
                  FStar_List.append uu____8115 [t2]
              | uu____8118 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___294_8123 = top  in
              let uu____8124 =
                let uu____8125 =
                  let uu____8136 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____8136, rhs)  in
                FStar_Parser_AST.Sum uu____8125  in
              {
                FStar_Parser_AST.tm = uu____8124;
                FStar_Parser_AST.range =
                  (uu___294_8123.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___294_8123.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8154 =
              let uu____8155 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8155  in
            (uu____8154, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8161 =
              let uu____8167 =
                let uu____8169 =
                  let uu____8171 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____8171 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____8169  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8167)  in
            FStar_Errors.raise_error uu____8161 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8186 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8186 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8193 =
                   let uu____8199 =
                     let uu____8201 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____8201
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8199)
                    in
                 FStar_Errors.raise_error uu____8193
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8216 =
                     let uu____8241 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8303 = desugar_term_aq env t  in
                               match uu____8303 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8241 FStar_List.unzip  in
                   (match uu____8216 with
                    | (args1,aqs) ->
                        let uu____8436 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8436, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8453)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8470 =
              let uu___295_8471 = top  in
              let uu____8472 =
                let uu____8473 =
                  let uu____8480 =
                    let uu___296_8481 = top  in
                    let uu____8482 =
                      let uu____8483 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8483  in
                    {
                      FStar_Parser_AST.tm = uu____8482;
                      FStar_Parser_AST.range =
                        (uu___296_8481.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___296_8481.FStar_Parser_AST.level)
                    }  in
                  (uu____8480, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8473  in
              {
                FStar_Parser_AST.tm = uu____8472;
                FStar_Parser_AST.range =
                  (uu___295_8471.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___295_8471.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8470
        | FStar_Parser_AST.Construct (n1,(a,uu____8491)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8511 =
                let uu___297_8512 = top  in
                let uu____8513 =
                  let uu____8514 =
                    let uu____8521 =
                      let uu___298_8522 = top  in
                      let uu____8523 =
                        let uu____8524 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8524  in
                      {
                        FStar_Parser_AST.tm = uu____8523;
                        FStar_Parser_AST.range =
                          (uu___298_8522.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___298_8522.FStar_Parser_AST.level)
                      }  in
                    (uu____8521, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8514  in
                {
                  FStar_Parser_AST.tm = uu____8513;
                  FStar_Parser_AST.range =
                    (uu___297_8512.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___297_8512.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8511))
        | FStar_Parser_AST.Construct (n1,(a,uu____8532)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8549 =
              let uu___299_8550 = top  in
              let uu____8551 =
                let uu____8552 =
                  let uu____8559 =
                    let uu___300_8560 = top  in
                    let uu____8561 =
                      let uu____8562 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8562  in
                    {
                      FStar_Parser_AST.tm = uu____8561;
                      FStar_Parser_AST.range =
                        (uu___300_8560.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___300_8560.FStar_Parser_AST.level)
                    }  in
                  (uu____8559, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8552  in
              {
                FStar_Parser_AST.tm = uu____8551;
                FStar_Parser_AST.range =
                  (uu___299_8550.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___299_8550.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8549
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8568; FStar_Ident.ident = uu____8569;
              FStar_Ident.nsstr = uu____8570; FStar_Ident.str = "Type0";_}
            ->
            let uu____8575 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8575, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8576; FStar_Ident.ident = uu____8577;
              FStar_Ident.nsstr = uu____8578; FStar_Ident.str = "Type";_}
            ->
            let uu____8583 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8583, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8584; FStar_Ident.ident = uu____8585;
               FStar_Ident.nsstr = uu____8586; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8606 =
              let uu____8607 =
                let uu____8608 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8608  in
              mk1 uu____8607  in
            (uu____8606, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8609; FStar_Ident.ident = uu____8610;
              FStar_Ident.nsstr = uu____8611; FStar_Ident.str = "Effect";_}
            ->
            let uu____8616 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8616, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8617; FStar_Ident.ident = uu____8618;
              FStar_Ident.nsstr = uu____8619; FStar_Ident.str = "True";_}
            ->
            let uu____8624 =
              let uu____8625 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8625
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8624, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8626; FStar_Ident.ident = uu____8627;
              FStar_Ident.nsstr = uu____8628; FStar_Ident.str = "False";_}
            ->
            let uu____8633 =
              let uu____8634 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8634
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8633, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8637;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8640 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8640 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8649 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8649, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8651 =
                    let uu____8653 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8653 txt
                     in
                  failwith uu____8651))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8662 = desugar_name mk1 setpos env true l  in
              (uu____8662, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8666 = desugar_name mk1 setpos env true l  in
              (uu____8666, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8679 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8679 with
                | FStar_Pervasives_Native.Some uu____8689 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8697 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8697 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8715 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8736 =
                    let uu____8737 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8737  in
                  (uu____8736, noaqs)
              | uu____8738 ->
                  let uu____8746 =
                    let uu____8752 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8752)  in
                  FStar_Errors.raise_error uu____8746
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8762 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8762 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8769 =
                    let uu____8775 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8775)
                     in
                  FStar_Errors.raise_error uu____8769
                    top.FStar_Parser_AST.range
              | uu____8783 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8787 = desugar_name mk1 setpos env true lid'  in
                  (uu____8787, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8804 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8804 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8823 ->
                       let uu____8830 =
                         FStar_Util.take
                           (fun uu____8854  ->
                              match uu____8854 with
                              | (uu____8860,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8830 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8905 =
                              let uu____8930 =
                                FStar_List.map
                                  (fun uu____8973  ->
                                     match uu____8973 with
                                     | (t,imp) ->
                                         let uu____8990 =
                                           desugar_term_aq env t  in
                                         (match uu____8990 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8930
                                FStar_List.unzip
                               in
                            (match uu____8905 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9133 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9133, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9152 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9152 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9163 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___255_9191  ->
                 match uu___255_9191 with
                 | FStar_Util.Inr uu____9197 -> true
                 | uu____9199 -> false) binders
            ->
            let terms =
              let uu____9208 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___256_9225  ->
                        match uu___256_9225 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9231 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9208 [t]  in
            let uu____9233 =
              let uu____9258 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9315 = desugar_typ_aq env t1  in
                        match uu____9315 with
                        | (t',aq) ->
                            let uu____9326 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9326, aq)))
                 in
              FStar_All.pipe_right uu____9258 FStar_List.unzip  in
            (match uu____9233 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9436 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9436
                    in
                 let uu____9445 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9445, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9472 =
              let uu____9489 =
                let uu____9496 =
                  let uu____9503 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9503]  in
                FStar_List.append binders uu____9496  in
              FStar_List.fold_left
                (fun uu____9556  ->
                   fun b  ->
                     match uu____9556 with
                     | (env1,tparams,typs) ->
                         let uu____9617 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9632 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9632)
                            in
                         (match uu____9617 with
                          | (xopt,t1) ->
                              let uu____9657 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9666 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9666)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9657 with
                               | (env2,x) ->
                                   let uu____9686 =
                                     let uu____9689 =
                                       let uu____9692 =
                                         let uu____9693 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9693
                                          in
                                       [uu____9692]  in
                                     FStar_List.append typs uu____9689  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___301_9719 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___301_9719.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___301_9719.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9686)))) (env, [], []) uu____9489
               in
            (match uu____9472 with
             | (env1,uu____9747,targs) ->
                 let tup =
                   let uu____9770 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9770
                    in
                 let uu____9771 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9771, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9790 = uncurry binders t  in
            (match uu____9790 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___257_9834 =
                   match uu___257_9834 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9851 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9851
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9875 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9875 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9908 = aux env [] bs  in (uu____9908, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9917 = desugar_binder env b  in
            (match uu____9917 with
             | (FStar_Pervasives_Native.None ,uu____9928) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9943 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9943 with
                  | ((x,uu____9959),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9972 =
                        let uu____9973 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9973  in
                      (uu____9972, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10052 = FStar_Util.set_is_empty i  in
                    if uu____10052
                    then
                      let uu____10057 = FStar_Util.set_union acc set1  in
                      aux uu____10057 sets2
                    else
                      (let uu____10062 =
                         let uu____10063 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10063  in
                       FStar_Pervasives_Native.Some uu____10062)
                 in
              let uu____10066 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10066 sets  in
            ((let uu____10070 = check_disjoint bvss  in
              match uu____10070 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10074 =
                    let uu____10080 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10080)
                     in
                  let uu____10084 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10074 uu____10084);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10092 =
                FStar_List.fold_left
                  (fun uu____10112  ->
                     fun pat  ->
                       match uu____10112 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10138,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10148 =
                                  let uu____10151 = free_type_vars env1 t  in
                                  FStar_List.append uu____10151 ftvs  in
                                (env1, uu____10148)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10156,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10167 =
                                  let uu____10170 = free_type_vars env1 t  in
                                  let uu____10173 =
                                    let uu____10176 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10176 ftvs  in
                                  FStar_List.append uu____10170 uu____10173
                                   in
                                (env1, uu____10167)
                            | uu____10181 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10092 with
              | (uu____10190,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10202 =
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
                    FStar_List.append uu____10202 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___258_10259 =
                    match uu___258_10259 with
                    | [] ->
                        let uu____10286 = desugar_term_aq env1 body  in
                        (match uu____10286 with
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
                               let uu____10396 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10396  in
                             (uu____10393, aq))
                    | p::rest ->
                        let uu____10411 = desugar_binding_pat env1 p  in
                        (match uu____10411 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10445)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10460 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10469 =
                               match b with
                               | LetBinder uu____10510 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10579) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10633 =
                                           let uu____10642 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10642, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10633
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10704,uu____10705) ->
                                              let tup2 =
                                                let uu____10707 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10707
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10712 =
                                                  let uu____10719 =
                                                    let uu____10720 =
                                                      let uu____10737 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10740 =
                                                        let uu____10751 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10760 =
                                                          let uu____10771 =
                                                            let uu____10780 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10780
                                                             in
                                                          [uu____10771]  in
                                                        uu____10751 ::
                                                          uu____10760
                                                         in
                                                      (uu____10737,
                                                        uu____10740)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10720
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10719
                                                   in
                                                uu____10712
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10831 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10831
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10882,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10884,pats)) ->
                                              let tupn =
                                                let uu____10929 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10929
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10942 =
                                                  let uu____10943 =
                                                    let uu____10960 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10963 =
                                                      let uu____10974 =
                                                        let uu____10985 =
                                                          let uu____10994 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10994
                                                           in
                                                        [uu____10985]  in
                                                      FStar_List.append args
                                                        uu____10974
                                                       in
                                                    (uu____10960,
                                                      uu____10963)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10943
                                                   in
                                                mk1 uu____10942  in
                                              let p2 =
                                                let uu____11042 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11042
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11089 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10469 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11183,uu____11184,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11206 =
                let uu____11207 = unparen e  in
                uu____11207.FStar_Parser_AST.tm  in
              match uu____11206 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11217 ->
                  let uu____11218 = desugar_term_aq env e  in
                  (match uu____11218 with
                   | (head1,aq) ->
                       let uu____11231 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11231, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11238 ->
            let rec aux args aqs e =
              let uu____11315 =
                let uu____11316 = unparen e  in
                uu____11316.FStar_Parser_AST.tm  in
              match uu____11315 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11334 = desugar_term_aq env t  in
                  (match uu____11334 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11382 ->
                  let uu____11383 = desugar_term_aq env e  in
                  (match uu____11383 with
                   | (head1,aq) ->
                       let uu____11404 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11404, (join_aqs (aq :: aqs))))
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
            let uu____11467 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11467
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
            let uu____11519 = desugar_term_aq env t  in
            (match uu____11519 with
             | (tm,s) ->
                 let uu____11530 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11530, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11536 =
              let uu____11549 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11549 then desugar_typ_aq else desugar_term_aq  in
            uu____11536 env1 e
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
                                             (id1,uu____12008);
                                           FStar_Parser_AST.prange =
                                             uu____12009;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12058 =
                                            let uu____12079 =
                                              let uu____12084 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12084  in
                                            (uu____12079, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12058, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12176) ->
                                        if top_level
                                        then
                                          let uu____12212 =
                                            let uu____12233 =
                                              let uu____12238 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12238  in
                                            (uu____12233, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12212, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
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
                  (fun uu____12435  ->
                     fun uu____12436  ->
                       match (uu____12435, uu____12436) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12544,uu____12545),uu____12546))
                           ->
                           let uu____12663 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12689 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12689 with
                                  | (env2,xx) ->
                                      let uu____12708 =
                                        let uu____12711 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12711 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12708))
                             | FStar_Util.Inr l ->
                                 let uu____12719 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12719, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12663 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12362 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12867 =
                    match uu____12867 with
                    | (attrs_opt,(uu____12903,args,result_t),def) ->
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
                                let uu____12991 = is_comp_type env1 t  in
                                if uu____12991
                                then
                                  ((let uu____12995 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13005 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13005))
                                       in
                                    match uu____12995 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13012 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13015 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13015))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13012
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
                          | uu____13026 ->
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
                              let uu____13041 =
                                let uu____13042 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13042
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13041
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
                  let uu____13123 = desugar_term_aq env' body  in
                  (match uu____13123 with
                   | (body1,aq) ->
                       let uu____13136 =
                         let uu____13139 =
                           let uu____13140 =
                             let uu____13154 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13154)  in
                           FStar_Syntax_Syntax.Tm_let uu____13140  in
                         FStar_All.pipe_left mk1 uu____13139  in
                       (uu____13136, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13229 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13229 with
              | (env1,binder,pat1) ->
                  let uu____13251 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13277 = desugar_term_aq env1 t2  in
                        (match uu____13277 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13291 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13291
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13292 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13292, aq))
                    | LocalBinder (x,uu____13325) ->
                        let uu____13326 = desugar_term_aq env1 t2  in
                        (match uu____13326 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13340;
                                    FStar_Syntax_Syntax.p = uu____13341;_},uu____13342)::[]
                                   -> body1
                               | uu____13355 ->
                                   let uu____13358 =
                                     let uu____13365 =
                                       let uu____13366 =
                                         let uu____13389 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13392 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13389, uu____13392)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13366
                                        in
                                     FStar_Syntax_Syntax.mk uu____13365  in
                                   uu____13358 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13432 =
                               let uu____13435 =
                                 let uu____13436 =
                                   let uu____13450 =
                                     let uu____13453 =
                                       let uu____13454 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13454]  in
                                     FStar_Syntax_Subst.close uu____13453
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13450)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13436  in
                               FStar_All.pipe_left mk1 uu____13435  in
                             (uu____13432, aq))
                     in
                  (match uu____13251 with | (tm,aq) -> (tm, aq))
               in
            let uu____13516 = FStar_List.hd lbs  in
            (match uu____13516 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13560 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13560
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13576 =
                let uu____13577 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13577  in
              mk1 uu____13576  in
            let uu____13578 = desugar_term_aq env t1  in
            (match uu____13578 with
             | (t1',aq1) ->
                 let uu____13589 = desugar_term_aq env t2  in
                 (match uu____13589 with
                  | (t2',aq2) ->
                      let uu____13600 = desugar_term_aq env t3  in
                      (match uu____13600 with
                       | (t3',aq3) ->
                           let uu____13611 =
                             let uu____13612 =
                               let uu____13613 =
                                 let uu____13636 =
                                   let uu____13653 =
                                     let uu____13668 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13668,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13682 =
                                     let uu____13699 =
                                       let uu____13714 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13714,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13699]  in
                                   uu____13653 :: uu____13682  in
                                 (t1', uu____13636)  in
                               FStar_Syntax_Syntax.Tm_match uu____13613  in
                             mk1 uu____13612  in
                           (uu____13611, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13910 =
              match uu____13910 with
              | (pat,wopt,b) ->
                  let uu____13932 = desugar_match_pat env pat  in
                  (match uu____13932 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13963 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13963
                          in
                       let uu____13968 = desugar_term_aq env1 b  in
                       (match uu____13968 with
                        | (b1,aq) ->
                            let uu____13981 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13981, aq)))
               in
            let uu____13986 = desugar_term_aq env e  in
            (match uu____13986 with
             | (e1,aq) ->
                 let uu____13997 =
                   let uu____14028 =
                     let uu____14061 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14061 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14028
                     (fun uu____14279  ->
                        match uu____14279 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13997 with
                  | (brs,aqs) ->
                      let uu____14498 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14498, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14532 =
              let uu____14553 = is_comp_type env t  in
              if uu____14553
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14608 = desugar_term_aq env t  in
                 match uu____14608 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14532 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14700 = desugar_term_aq env e  in
                 (match uu____14700 with
                  | (e1,aq) ->
                      let uu____14711 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14711, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14750,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14793 = FStar_List.hd fields  in
              match uu____14793 with | (f,uu____14805) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14851  ->
                        match uu____14851 with
                        | (g,uu____14858) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14865,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14879 =
                         let uu____14885 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14885)
                          in
                       FStar_Errors.raise_error uu____14879
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
                  let uu____14896 =
                    let uu____14907 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14938  ->
                              match uu____14938 with
                              | (f,uu____14948) ->
                                  let uu____14949 =
                                    let uu____14950 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____14950
                                     in
                                  (uu____14949, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14907)  in
                  FStar_Parser_AST.Construct uu____14896
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____14968 =
                      let uu____14969 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____14969  in
                    FStar_Parser_AST.mk_term uu____14968
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____14971 =
                      let uu____14984 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15014  ->
                                match uu____15014 with
                                | (f,uu____15024) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____14984)  in
                    FStar_Parser_AST.Record uu____14971  in
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
            let uu____15084 = desugar_term_aq env recterm1  in
            (match uu____15084 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15100;
                         FStar_Syntax_Syntax.vars = uu____15101;_},args)
                      ->
                      let uu____15127 =
                        let uu____15128 =
                          let uu____15129 =
                            let uu____15146 =
                              let uu____15149 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15150 =
                                let uu____15153 =
                                  let uu____15154 =
                                    let uu____15161 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15161)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15154
                                   in
                                FStar_Pervasives_Native.Some uu____15153  in
                              FStar_Syntax_Syntax.fvar uu____15149
                                FStar_Syntax_Syntax.delta_constant
                                uu____15150
                               in
                            (uu____15146, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15129  in
                        FStar_All.pipe_left mk1 uu____15128  in
                      (uu____15127, s)
                  | uu____15190 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15194 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15194 with
              | (constrname,is_rec) ->
                  let uu____15213 = desugar_term_aq env e  in
                  (match uu____15213 with
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
                       let uu____15233 =
                         let uu____15234 =
                           let uu____15235 =
                             let uu____15252 =
                               let uu____15255 =
                                 let uu____15256 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15256
                                  in
                               FStar_Syntax_Syntax.fvar uu____15255
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15258 =
                               let uu____15269 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15269]  in
                             (uu____15252, uu____15258)  in
                           FStar_Syntax_Syntax.Tm_app uu____15235  in
                         FStar_All.pipe_left mk1 uu____15234  in
                       (uu____15233, s))))
        | FStar_Parser_AST.NamedTyp (uu____15306,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15316 =
              let uu____15317 = FStar_Syntax_Subst.compress tm  in
              uu____15317.FStar_Syntax_Syntax.n  in
            (match uu____15316 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15325 =
                   let uu___302_15326 =
                     let uu____15327 =
                       let uu____15329 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15329  in
                     FStar_Syntax_Util.exp_string uu____15327  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___302_15326.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___302_15326.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15325, noaqs)
             | uu____15330 ->
                 let uu____15331 =
                   let uu____15337 =
                     let uu____15339 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____15339
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15337)  in
                 FStar_Errors.raise_error uu____15331
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15348 = desugar_term_aq env e  in
            (match uu____15348 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15360 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15360, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15365 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15366 =
              let uu____15367 =
                let uu____15374 = desugar_term env e  in (bv, uu____15374)
                 in
              [uu____15367]  in
            (uu____15365, uu____15366)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15399 =
              let uu____15400 =
                let uu____15401 =
                  let uu____15408 = desugar_term env e  in (uu____15408, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15401  in
              FStar_All.pipe_left mk1 uu____15400  in
            (uu____15399, noaqs)
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
              let uu____15437 =
                let uu____15438 =
                  let uu____15445 =
                    let uu____15446 =
                      let uu____15447 =
                        let uu____15456 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15469 =
                          let uu____15470 =
                            let uu____15471 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15471  in
                          FStar_Parser_AST.mk_term uu____15470
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15456, uu____15469,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15447  in
                    FStar_Parser_AST.mk_term uu____15446
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15445)  in
                FStar_Parser_AST.Abs uu____15438  in
              FStar_Parser_AST.mk_term uu____15437
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
                   fun uu____15517  ->
                     match uu____15517 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____15521 =
                           let uu____15528 =
                             let uu____15533 = eta_and_annot rel2  in
                             (uu____15533, FStar_Parser_AST.Nothing)  in
                           let uu____15534 =
                             let uu____15541 =
                               let uu____15548 =
                                 let uu____15553 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____15553, FStar_Parser_AST.Nothing)  in
                               let uu____15554 =
                                 let uu____15561 =
                                   let uu____15566 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____15566, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____15561]  in
                               uu____15548 :: uu____15554  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____15541
                              in
                           uu____15528 :: uu____15534  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____15521
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              FStar_Parser_AST.mkApp finish1 [(e1, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____15596 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15597 = desugar_formula env top  in
            (uu____15597, noaqs)
        | uu____15598 ->
            let uu____15599 =
              let uu____15605 =
                let uu____15607 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____15607  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15605)  in
            FStar_Errors.raise_error uu____15599 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15617 -> false
    | uu____15627 -> true

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
           (fun uu____15665  ->
              match uu____15665 with
              | (a,imp) ->
                  let uu____15678 = desugar_term env a  in
                  arg_withimp_e imp uu____15678))

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
          let is_requires uu____15715 =
            match uu____15715 with
            | (t1,uu____15722) ->
                let uu____15723 =
                  let uu____15724 = unparen t1  in
                  uu____15724.FStar_Parser_AST.tm  in
                (match uu____15723 with
                 | FStar_Parser_AST.Requires uu____15726 -> true
                 | uu____15735 -> false)
             in
          let is_ensures uu____15747 =
            match uu____15747 with
            | (t1,uu____15754) ->
                let uu____15755 =
                  let uu____15756 = unparen t1  in
                  uu____15756.FStar_Parser_AST.tm  in
                (match uu____15755 with
                 | FStar_Parser_AST.Ensures uu____15758 -> true
                 | uu____15767 -> false)
             in
          let is_app head1 uu____15785 =
            match uu____15785 with
            | (t1,uu____15793) ->
                let uu____15794 =
                  let uu____15795 = unparen t1  in
                  uu____15795.FStar_Parser_AST.tm  in
                (match uu____15794 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15798;
                        FStar_Parser_AST.level = uu____15799;_},uu____15800,uu____15801)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15803 -> false)
             in
          let is_smt_pat uu____15815 =
            match uu____15815 with
            | (t1,uu____15822) ->
                let uu____15823 =
                  let uu____15824 = unparen t1  in
                  uu____15824.FStar_Parser_AST.tm  in
                (match uu____15823 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____15828);
                               FStar_Parser_AST.range = uu____15829;
                               FStar_Parser_AST.level = uu____15830;_},uu____15831)::uu____15832::[])
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
                               FStar_Parser_AST.range = uu____15881;
                               FStar_Parser_AST.level = uu____15882;_},uu____15883)::uu____15884::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____15917 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____15952 = head_and_args t1  in
            match uu____15952 with
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
                     let thunk_ens uu____16045 =
                       match uu____16045 with
                       | (e,i) ->
                           let uu____16056 = FStar_Parser_AST.thunk e  in
                           (uu____16056, i)
                        in
                     let fail_lemma uu____16068 =
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
                           (Prims.strcat
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
                           let uu____16174 =
                             let uu____16181 =
                               let uu____16188 = thunk_ens ens  in
                               [uu____16188; nil_pat]  in
                             req_true :: uu____16181  in
                           unit_tm :: uu____16174
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16235 =
                             let uu____16242 =
                               let uu____16249 = thunk_ens ens  in
                               [uu____16249; nil_pat]  in
                             req :: uu____16242  in
                           unit_tm :: uu____16235
                       | ens::smtpat::[] when
                           (((let uu____16298 = is_requires ens  in
                              Prims.op_Negation uu____16298) &&
                               (let uu____16301 = is_smt_pat ens  in
                                Prims.op_Negation uu____16301))
                              &&
                              (let uu____16304 = is_decreases ens  in
                               Prims.op_Negation uu____16304))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16306 =
                             let uu____16313 =
                               let uu____16320 = thunk_ens ens  in
                               [uu____16320; smtpat]  in
                             req_true :: uu____16313  in
                           unit_tm :: uu____16306
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16367 =
                             let uu____16374 =
                               let uu____16381 = thunk_ens ens  in
                               [uu____16381; nil_pat; dec]  in
                             req_true :: uu____16374  in
                           unit_tm :: uu____16367
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16441 =
                             let uu____16448 =
                               let uu____16455 = thunk_ens ens  in
                               [uu____16455; smtpat; dec]  in
                             req_true :: uu____16448  in
                           unit_tm :: uu____16441
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16515 =
                             let uu____16522 =
                               let uu____16529 = thunk_ens ens  in
                               [uu____16529; nil_pat; dec]  in
                             req :: uu____16522  in
                           unit_tm :: uu____16515
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16589 =
                             let uu____16596 =
                               let uu____16603 = thunk_ens ens  in
                               [uu____16603; smtpat]  in
                             req :: uu____16596  in
                           unit_tm :: uu____16589
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16668 =
                             let uu____16675 =
                               let uu____16682 = thunk_ens ens  in
                               [uu____16682; dec; smtpat]  in
                             req :: uu____16675  in
                           unit_tm :: uu____16668
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16744 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16744, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16772 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16772
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16775 =
                       let uu____16782 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16782, [])  in
                     (uu____16775, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16800 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16800
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16803 =
                       let uu____16810 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16810, [])  in
                     (uu____16803, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____16832 =
                       let uu____16839 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16839, [])  in
                     (uu____16832, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16862 when allow_type_promotion ->
                     let default_effect =
                       let uu____16864 = FStar_Options.ml_ish ()  in
                       if uu____16864
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16870 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____16870
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____16877 =
                       let uu____16884 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16884, [])  in
                     (uu____16877, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16907 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____16926 = pre_process_comp_typ t  in
          match uu____16926 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____16978 =
                    let uu____16984 =
                      let uu____16986 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____16986
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____16984)
                     in
                  fail1 uu____16978)
               else ();
               (let is_universe uu____17002 =
                  match uu____17002 with
                  | (uu____17008,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17010 = FStar_Util.take is_universe args  in
                match uu____17010 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17069  ->
                           match uu____17069 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17076 =
                      let uu____17091 = FStar_List.hd args1  in
                      let uu____17100 = FStar_List.tl args1  in
                      (uu____17091, uu____17100)  in
                    (match uu____17076 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17155 =
                           let is_decrease uu____17194 =
                             match uu____17194 with
                             | (t1,uu____17205) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17216;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17217;_},uu____17218::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17257 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17155 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17374  ->
                                        match uu____17374 with
                                        | (t1,uu____17384) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17393,(arg,uu____17395)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17434 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17455 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17467 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17467
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17474 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17474
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags1 =
                                      let uu____17484 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17484
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17491 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17491
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17498 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17498
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17505 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17505
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags2 =
                                      FStar_List.append flags1 cattributes
                                       in
                                    let rest3 =
                                      let uu____17526 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17526
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
                                                    let uu____17617 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17617
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
                                              | uu____17638 -> pat  in
                                            let uu____17639 =
                                              let uu____17650 =
                                                let uu____17661 =
                                                  let uu____17670 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17670, aq)  in
                                                [uu____17661]  in
                                              ens :: uu____17650  in
                                            req :: uu____17639
                                        | uu____17711 -> rest2
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
                                          (FStar_List.append flags2
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
        | uu____17743 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___303_17765 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___303_17765.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___303_17765.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___304_17807 = b  in
             {
               FStar_Parser_AST.b = (uu___304_17807.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___304_17807.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___304_17807.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____17870 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____17870)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17883 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17883 with
             | (env1,a1) ->
                 let a2 =
                   let uu___305_17893 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___305_17893.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___305_17893.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____17919 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____17933 =
                     let uu____17936 =
                       let uu____17937 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____17937]  in
                     no_annot_abs uu____17936 body2  in
                   FStar_All.pipe_left setpos uu____17933  in
                 let uu____17958 =
                   let uu____17959 =
                     let uu____17976 =
                       let uu____17979 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____17979
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____17981 =
                       let uu____17992 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____17992]  in
                     (uu____17976, uu____17981)  in
                   FStar_Syntax_Syntax.Tm_app uu____17959  in
                 FStar_All.pipe_left mk1 uu____17958)
        | uu____18031 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18112 = q (rest, pats, body)  in
              let uu____18119 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18112 uu____18119
                FStar_Parser_AST.Formula
               in
            let uu____18120 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18120 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18129 -> failwith "impossible"  in
      let uu____18133 =
        let uu____18134 = unparen f  in uu____18134.FStar_Parser_AST.tm  in
      match uu____18133 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18147,uu____18148) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18160,uu____18161) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18193 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18193
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18229 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18229
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18273 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18278 =
        FStar_List.fold_left
          (fun uu____18311  ->
             fun b  ->
               match uu____18311 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___306_18355 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___306_18355.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___306_18355.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___306_18355.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18370 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18370 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___307_18388 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___307_18388.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___307_18388.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18389 =
                               let uu____18396 =
                                 let uu____18401 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18401)  in
                               uu____18396 :: out  in
                             (env2, uu____18389))
                    | uu____18412 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18278 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18485 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18485)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18490 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18490)
      | FStar_Parser_AST.TVariable x ->
          let uu____18494 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18494)
      | FStar_Parser_AST.NoName t ->
          let uu____18498 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18498)
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
      fun uu___259_18506  ->
        match uu___259_18506 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18528 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18528, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18545 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18545 with
             | (env1,a1) ->
                 let uu____18562 =
                   let uu____18569 = trans_aqual env1 imp  in
                   ((let uu___308_18575 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___308_18575.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___308_18575.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18569)
                    in
                 (uu____18562, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___260_18583  ->
      match uu___260_18583 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18587 =
            let uu____18588 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18588  in
          FStar_Pervasives_Native.Some uu____18587
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18604) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18606) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18609 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18627 = binder_ident b  in
         FStar_Common.list_of_option uu____18627) bs
  
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
               (fun uu___261_18664  ->
                  match uu___261_18664 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18669 -> false))
           in
        let quals2 q =
          let uu____18683 =
            (let uu____18687 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18687) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18683
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18704 = FStar_Ident.range_of_lid disc_name  in
                let uu____18705 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18704;
                  FStar_Syntax_Syntax.sigquals = uu____18705;
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
            let uu____18745 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18783  ->
                        match uu____18783 with
                        | (x,uu____18794) ->
                            let uu____18799 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18799 with
                             | (field_name,uu____18807) ->
                                 let only_decl =
                                   ((let uu____18812 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18812)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18814 =
                                        let uu____18816 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18816.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18814)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____18834 =
                                       FStar_List.filter
                                         (fun uu___262_18838  ->
                                            match uu___262_18838 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____18841 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____18834
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___263_18856  ->
                                             match uu___263_18856 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____18861 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____18864 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____18864;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____18871 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____18871
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____18882 =
                                        let uu____18887 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____18887  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____18882;
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
                                      let uu____18891 =
                                        let uu____18892 =
                                          let uu____18899 =
                                            let uu____18902 =
                                              let uu____18903 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____18903
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____18902]  in
                                          ((false, [lb]), uu____18899)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____18892
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____18891;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18745 FStar_List.flatten
  
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
            (lid,uu____18952,t,uu____18954,n1,uu____18956) when
            let uu____18963 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____18963 ->
            let uu____18965 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____18965 with
             | (formals,uu____18983) ->
                 (match formals with
                  | [] -> []
                  | uu____19012 ->
                      let filter_records uu___264_19028 =
                        match uu___264_19028 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19031,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19043 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19045 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19045 with
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
                      let uu____19057 = FStar_Util.first_N n1 formals  in
                      (match uu____19057 with
                       | (uu____19086,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19120 -> []
  
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
                    let uu____19199 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19199
                    then
                      let uu____19205 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19205
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19209 =
                      let uu____19214 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19214  in
                    let uu____19215 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19221 =
                          let uu____19224 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19224  in
                        FStar_Syntax_Util.arrow typars uu____19221
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19229 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19209;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19215;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19229;
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
          let tycon_id uu___265_19283 =
            match uu___265_19283 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19285,uu____19286) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19296,uu____19297,uu____19298) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19308,uu____19309,uu____19310) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19340,uu____19341,uu____19342) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19388) ->
                let uu____19389 =
                  let uu____19390 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19390  in
                FStar_Parser_AST.mk_term uu____19389 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19392 =
                  let uu____19393 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19393  in
                FStar_Parser_AST.mk_term uu____19392 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19395) ->
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
              | uu____19426 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19434 =
                     let uu____19435 =
                       let uu____19442 = binder_to_term b  in
                       (out, uu____19442, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19435  in
                   FStar_Parser_AST.mk_term uu____19434
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___266_19454 =
            match uu___266_19454 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19511  ->
                       match uu____19511 with
                       | (x,t,uu____19522) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19528 =
                    let uu____19529 =
                      let uu____19530 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19530  in
                    FStar_Parser_AST.mk_term uu____19529
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19528 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19537 = binder_idents parms  in id1 ::
                    uu____19537
                   in
                (FStar_List.iter
                   (fun uu____19555  ->
                      match uu____19555 with
                      | (f,uu____19565,uu____19566) ->
                          let uu____19571 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19571
                          then
                            let uu____19576 =
                              let uu____19582 =
                                let uu____19584 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19584
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19582)
                               in
                            FStar_Errors.raise_error uu____19576
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19590 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19617  ->
                            match uu____19617 with
                            | (x,uu____19627,uu____19628) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19590)))
            | uu____19686 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___267_19726 =
            match uu___267_19726 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19750 = typars_of_binders _env binders  in
                (match uu____19750 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19786 =
                         let uu____19787 =
                           let uu____19788 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19788  in
                         FStar_Parser_AST.mk_term uu____19787
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19786 binders  in
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
            | uu____19799 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____19842 =
              FStar_List.fold_left
                (fun uu____19876  ->
                   fun uu____19877  ->
                     match (uu____19876, uu____19877) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____19946 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____19946 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____19842 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20037 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20037
                | uu____20038 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20046 = desugar_abstract_tc quals env [] tc  in
              (match uu____20046 with
               | (uu____20059,uu____20060,se,uu____20062) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20065,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20084 =
                                 let uu____20086 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20086  in
                               if uu____20084
                               then
                                 let uu____20089 =
                                   let uu____20095 =
                                     let uu____20097 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20097
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20095)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20089
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
                           | uu____20110 ->
                               let uu____20111 =
                                 let uu____20118 =
                                   let uu____20119 =
                                     let uu____20134 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20134)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20119
                                    in
                                 FStar_Syntax_Syntax.mk uu____20118  in
                               uu____20111 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___309_20150 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___309_20150.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___309_20150.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___309_20150.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20151 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20155 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20155
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20168 = typars_of_binders env binders  in
              (match uu____20168 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20202 =
                           FStar_Util.for_some
                             (fun uu___268_20205  ->
                                match uu___268_20205 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20208 -> false) quals
                            in
                         if uu____20202
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20216 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20216
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20221 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___269_20227  ->
                               match uu___269_20227 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20230 -> false))
                        in
                     if uu____20221
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20244 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20244
                     then
                       let uu____20250 =
                         let uu____20257 =
                           let uu____20258 = unparen t  in
                           uu____20258.FStar_Parser_AST.tm  in
                         match uu____20257 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20279 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20309)::args_rev ->
                                   let uu____20321 =
                                     let uu____20322 = unparen last_arg  in
                                     uu____20322.FStar_Parser_AST.tm  in
                                   (match uu____20321 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20350 -> ([], args))
                               | uu____20359 -> ([], args)  in
                             (match uu____20279 with
                              | (cattributes,args1) ->
                                  let uu____20398 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20398))
                         | uu____20409 -> (t, [])  in
                       match uu____20250 with
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
                                  (fun uu___270_20432  ->
                                     match uu___270_20432 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20435 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20444)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20468 = tycon_record_as_variant trec  in
              (match uu____20468 with
               | (t,fs) ->
                   let uu____20485 =
                     let uu____20488 =
                       let uu____20489 =
                         let uu____20498 =
                           let uu____20501 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20501  in
                         (uu____20498, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20489  in
                     uu____20488 :: quals  in
                   desugar_tycon env d uu____20485 [t])
          | uu____20506::uu____20507 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20677 = et  in
                match uu____20677 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20907 ->
                         let trec = tc  in
                         let uu____20931 = tycon_record_as_variant trec  in
                         (match uu____20931 with
                          | (t,fs) ->
                              let uu____20991 =
                                let uu____20994 =
                                  let uu____20995 =
                                    let uu____21004 =
                                      let uu____21007 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21007  in
                                    (uu____21004, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____20995
                                   in
                                uu____20994 :: quals1  in
                              collect_tcs uu____20991 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21097 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21097 with
                          | (env2,uu____21158,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21311 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21311 with
                          | (env2,uu____21372,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21500 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21550 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21550 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___272_22065  ->
                             match uu___272_22065 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22131,uu____22132);
                                    FStar_Syntax_Syntax.sigrng = uu____22133;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22134;
                                    FStar_Syntax_Syntax.sigmeta = uu____22135;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22136;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22200 =
                                     typars_of_binders env1 binders  in
                                   match uu____22200 with
                                   | (env2,tpars1) ->
                                       let uu____22227 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22227 with
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
                                 let uu____22256 =
                                   let uu____22275 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22275)
                                    in
                                 [uu____22256]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22335);
                                    FStar_Syntax_Syntax.sigrng = uu____22336;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22338;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22339;_},constrs,tconstr,quals1)
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
                                 let uu____22440 = push_tparams env1 tpars
                                    in
                                 (match uu____22440 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22507  ->
                                             match uu____22507 with
                                             | (x,uu____22519) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22524 =
                                        let uu____22551 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22661  ->
                                                  match uu____22661 with
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
                                                        let uu____22721 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22721
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
                                                                uu___271_22732
                                                                 ->
                                                                match uu___271_22732
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22744
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22752 =
                                                        let uu____22771 =
                                                          let uu____22772 =
                                                            let uu____22773 =
                                                              let uu____22789
                                                                =
                                                                let uu____22790
                                                                  =
                                                                  let uu____22793
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22793
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22790
                                                                 in
                                                              (name, univs1,
                                                                uu____22789,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22773
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22772;
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
                                                          uu____22771)
                                                         in
                                                      (name, uu____22752)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22551
                                         in
                                      (match uu____22524 with
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
                             | uu____23009 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23137  ->
                             match uu____23137 with
                             | (name_doc,uu____23163,uu____23164) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23236  ->
                             match uu____23236 with
                             | (uu____23255,uu____23256,se) -> se))
                      in
                   let uu____23282 =
                     let uu____23289 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23289 rng
                      in
                   (match uu____23282 with
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
                               (fun uu____23351  ->
                                  match uu____23351 with
                                  | (uu____23372,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23419,tps,k,uu____23422,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
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
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____23444 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23461  ->
                                 match uu____23461 with
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
      let uu____23506 =
        FStar_List.fold_left
          (fun uu____23541  ->
             fun b  ->
               match uu____23541 with
               | (env1,binders1) ->
                   let uu____23585 = desugar_binder env1 b  in
                   (match uu____23585 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23608 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23608 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23661 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23506 with
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
          let uu____23765 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___273_23772  ->
                    match uu___273_23772 with
                    | FStar_Syntax_Syntax.Reflectable uu____23774 -> true
                    | uu____23776 -> false))
             in
          if uu____23765
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____23781 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____23781
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
      let uu____23822 = FStar_Syntax_Util.head_and_args at1  in
      match uu____23822 with
      | (hd1,args) ->
          let uu____23875 =
            let uu____23890 =
              let uu____23891 = FStar_Syntax_Subst.compress hd1  in
              uu____23891.FStar_Syntax_Syntax.n  in
            (uu____23890, args)  in
          (match uu____23875 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____23916)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____23951 =
                 let uu____23956 =
                   let uu____23965 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____23965 a1  in
                 uu____23956 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____23951 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____23995 =
                      let uu____24004 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24004, b)  in
                    FStar_Pervasives_Native.Some uu____23995
                | uu____24021 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24075) when
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
           | uu____24110 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24282 = desugar_binders monad_env eff_binders  in
                  match uu____24282 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24322 =
                          let uu____24324 =
                            let uu____24333 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24333  in
                          FStar_List.length uu____24324  in
                        uu____24322 = (Prims.parse_int "1")  in
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
                            (uu____24417,uu____24418,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24420,uu____24421,uu____24422),uu____24423)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24460 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24463 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24475 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24475 mandatory_members)
                          eff_decls
                         in
                      (match uu____24463 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24494 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24523  ->
                                     fun decl  ->
                                       match uu____24523 with
                                       | (env2,out) ->
                                           let uu____24543 =
                                             desugar_decl env2 decl  in
                                           (match uu____24543 with
                                            | (env3,ses) ->
                                                let uu____24556 =
                                                  let uu____24559 =
                                                    FStar_List.hd ses  in
                                                  uu____24559 :: out  in
                                                (env3, uu____24556)))
                                  (env1, []))
                              in
                           (match uu____24494 with
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
                                              (uu____24628,uu____24629,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24632,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____24633,(def,uu____24635)::
                                                      (cps_type,uu____24637)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____24638;
                                                   FStar_Parser_AST.level =
                                                     uu____24639;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____24695 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24695 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24733 =
                                                     let uu____24734 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24735 =
                                                       let uu____24736 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24736
                                                        in
                                                     let uu____24743 =
                                                       let uu____24744 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24744
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24734;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24735;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____24743
                                                     }  in
                                                   (uu____24733, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____24753,uu____24754,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24757,defn),doc1)::[])
                                              when for_free ->
                                              let uu____24796 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24796 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24834 =
                                                     let uu____24835 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24836 =
                                                       let uu____24837 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24837
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24835;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24836;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24834, doc1))
                                          | uu____24846 ->
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
                                    let uu____24882 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24882
                                     in
                                  let uu____24884 =
                                    let uu____24885 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____24885
                                     in
                                  ([], uu____24884)  in
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
                                      let uu____24903 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____24903)  in
                                    let uu____24910 =
                                      let uu____24911 =
                                        let uu____24912 =
                                          let uu____24913 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____24913
                                           in
                                        let uu____24923 = lookup1 "return"
                                           in
                                        let uu____24925 = lookup1 "bind"  in
                                        let uu____24927 =
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
                                            uu____24912;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____24923;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____24925;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____24927
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____24911
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____24910;
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
                                         (fun uu___274_24935  ->
                                            match uu___274_24935 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____24938 -> true
                                            | uu____24940 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____24955 =
                                       let uu____24956 =
                                         let uu____24957 =
                                           lookup1 "return_wp"  in
                                         let uu____24959 = lookup1 "bind_wp"
                                            in
                                         let uu____24961 =
                                           lookup1 "if_then_else"  in
                                         let uu____24963 = lookup1 "ite_wp"
                                            in
                                         let uu____24965 = lookup1 "stronger"
                                            in
                                         let uu____24967 = lookup1 "close_wp"
                                            in
                                         let uu____24969 = lookup1 "assert_p"
                                            in
                                         let uu____24971 = lookup1 "assume_p"
                                            in
                                         let uu____24973 = lookup1 "null_wp"
                                            in
                                         let uu____24975 = lookup1 "trivial"
                                            in
                                         let uu____24977 =
                                           if rr
                                           then
                                             let uu____24979 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____24979
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____24997 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25002 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25007 =
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
                                             uu____24957;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____24959;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____24961;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____24963;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____24965;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____24967;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____24969;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____24971;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____24973;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____24975;
                                           FStar_Syntax_Syntax.repr =
                                             uu____24977;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____24997;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25002;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25007
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____24956
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____24955;
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
                                          fun uu____25033  ->
                                            match uu____25033 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25047 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25047
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
                let uu____25071 = desugar_binders env1 eff_binders  in
                match uu____25071 with
                | (env2,binders) ->
                    let uu____25108 =
                      let uu____25119 = head_and_args defn  in
                      match uu____25119 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25156 ->
                                let uu____25157 =
                                  let uu____25163 =
                                    let uu____25165 =
                                      let uu____25167 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____25167 " not found"
                                       in
                                    Prims.strcat "Effect " uu____25165  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25163)
                                   in
                                FStar_Errors.raise_error uu____25157
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25173 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25203)::args_rev ->
                                let uu____25215 =
                                  let uu____25216 = unparen last_arg  in
                                  uu____25216.FStar_Parser_AST.tm  in
                                (match uu____25215 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25244 -> ([], args))
                            | uu____25253 -> ([], args)  in
                          (match uu____25173 with
                           | (cattributes,args1) ->
                               let uu____25296 = desugar_args env2 args1  in
                               let uu____25297 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25296, uu____25297))
                       in
                    (match uu____25108 with
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
                          (let uu____25337 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25337 with
                           | (ed_binders,uu____25351,ed_binders_opening) ->
                               let sub1 uu____25364 =
                                 match uu____25364 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25378 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25378 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25382 =
                                       let uu____25383 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25383)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25382
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25392 =
                                   let uu____25393 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25393
                                    in
                                 let uu____25408 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25409 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25410 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25411 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25412 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25413 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25414 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25415 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25416 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25417 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25418 =
                                   let uu____25419 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25419
                                    in
                                 let uu____25434 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25435 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25436 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____25444 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25445 =
                                          let uu____25446 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25446
                                           in
                                        let uu____25461 =
                                          let uu____25462 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25462
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25444;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25445;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25461
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
                                     uu____25392;
                                   FStar_Syntax_Syntax.ret_wp = uu____25408;
                                   FStar_Syntax_Syntax.bind_wp = uu____25409;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25410;
                                   FStar_Syntax_Syntax.ite_wp = uu____25411;
                                   FStar_Syntax_Syntax.stronger = uu____25412;
                                   FStar_Syntax_Syntax.close_wp = uu____25413;
                                   FStar_Syntax_Syntax.assert_p = uu____25414;
                                   FStar_Syntax_Syntax.assume_p = uu____25415;
                                   FStar_Syntax_Syntax.null_wp = uu____25416;
                                   FStar_Syntax_Syntax.trivial = uu____25417;
                                   FStar_Syntax_Syntax.repr = uu____25418;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25434;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25435;
                                   FStar_Syntax_Syntax.actions = uu____25436;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25480 =
                                     let uu____25482 =
                                       let uu____25491 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25491
                                        in
                                     FStar_List.length uu____25482  in
                                   uu____25480 = (Prims.parse_int "1")  in
                                 let uu____25524 =
                                   let uu____25527 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25527 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25524;
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
                                             let uu____25551 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25551
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25553 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25553
                                 then
                                   let reflect_lid =
                                     let uu____25560 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25560
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
    let uu____25572 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25572 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25657 ->
              let uu____25660 =
                let uu____25662 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25662
                 in
              Prims.strcat "\n  " uu____25660
          | uu____25665 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25684  ->
               match uu____25684 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text))
           in
        let fv =
          let uu____25729 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25729
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25732 =
          let uu____25743 = FStar_Syntax_Syntax.as_arg arg  in [uu____25743]
           in
        FStar_Syntax_Util.mk_app fv uu____25732

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25774 = desugar_decl_noattrs env d  in
      match uu____25774 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25792 = mk_comment_attr d  in uu____25792 :: attrs1  in
          let uu____25793 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___310_25803 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___310_25803.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___310_25803.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___310_25803.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___310_25803.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___311_25806 = sigelt  in
                      let uu____25807 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____25813 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____25813) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___311_25806.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___311_25806.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___311_25806.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___311_25806.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25807
                      })) sigelts
             in
          (env1, uu____25793)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25839 = desugar_decl_aux env d  in
      match uu____25839 with
      | (env1,ses) ->
          let uu____25850 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____25850)

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
      | FStar_Parser_AST.Fsdoc uu____25878 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____25883 = FStar_Syntax_DsEnv.iface env  in
          if uu____25883
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____25898 =
               let uu____25900 =
                 let uu____25902 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____25903 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____25902
                   uu____25903
                  in
               Prims.op_Negation uu____25900  in
             if uu____25898
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____25917 =
                  let uu____25919 =
                    let uu____25921 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____25921 lid  in
                  Prims.op_Negation uu____25919  in
                if uu____25917
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____25935 =
                     let uu____25937 =
                       let uu____25939 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____25939
                         lid
                        in
                     Prims.op_Negation uu____25937  in
                   if uu____25935
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____25957 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____25957, [])
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
              | (FStar_Parser_AST.TyconRecord uu____25998,uu____25999)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26038 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26065  ->
                 match uu____26065 with | (x,uu____26073) -> x) tcs
             in
          let uu____26078 =
            let uu____26083 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26083 tcs1  in
          (match uu____26078 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26100 =
                   let uu____26101 =
                     let uu____26108 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26108  in
                   [uu____26101]  in
                 let uu____26121 =
                   let uu____26124 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26127 =
                     let uu____26138 =
                       let uu____26147 =
                         let uu____26148 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26148  in
                       FStar_Syntax_Syntax.as_arg uu____26147  in
                     [uu____26138]  in
                   FStar_Syntax_Util.mk_app uu____26124 uu____26127  in
                 FStar_Syntax_Util.abs uu____26100 uu____26121
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26188,id1))::uu____26190 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26193::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26197 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26197 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26203 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26203]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26224) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26234,uu____26235,uu____26236,uu____26237,uu____26238)
                     ->
                     let uu____26247 =
                       let uu____26248 =
                         let uu____26249 =
                           let uu____26256 = mkclass lid  in
                           (meths, uu____26256)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26249  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26248;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26247]
                 | uu____26259 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26293;
                    FStar_Parser_AST.prange = uu____26294;_},uu____26295)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26305;
                    FStar_Parser_AST.prange = uu____26306;_},uu____26307)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26323;
                         FStar_Parser_AST.prange = uu____26324;_},uu____26325);
                    FStar_Parser_AST.prange = uu____26326;_},uu____26327)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26349;
                         FStar_Parser_AST.prange = uu____26350;_},uu____26351);
                    FStar_Parser_AST.prange = uu____26352;_},uu____26353)::[]
                   -> false
               | (p,uu____26382)::[] ->
                   let uu____26391 = is_app_pattern p  in
                   Prims.op_Negation uu____26391
               | uu____26393 -> false)
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
            let uu____26468 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26468 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26481 =
                     let uu____26482 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26482.FStar_Syntax_Syntax.n  in
                   match uu____26481 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26492) ->
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
                         | uu____26528::uu____26529 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26532 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___275_26548  ->
                                     match uu___275_26548 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26551;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26552;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26553;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26554;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26555;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26556;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26557;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26569;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26570;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26571;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26572;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26573;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26574;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26588 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26621  ->
                                   match uu____26621 with
                                   | (uu____26635,(uu____26636,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26588
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26656 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26656
                         then
                           let uu____26662 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___312_26677 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___313_26679 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___313_26679.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___313_26679.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___312_26677.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26662)
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
                   | uu____26709 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26717 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26736 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26717 with
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
                       let uu___314_26773 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___314_26773.FStar_Parser_AST.prange)
                       }
                   | uu____26780 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___315_26787 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___315_26787.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___315_26787.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___315_26787.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____26823 id1 =
                   match uu____26823 with
                   | (env1,ses) ->
                       let main =
                         let uu____26844 =
                           let uu____26845 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____26845  in
                         FStar_Parser_AST.mk_term uu____26844
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
                       let uu____26895 = desugar_decl env1 id_decl  in
                       (match uu____26895 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____26913 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____26913 FStar_Util.set_elements
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
            let uu____26937 = close_fun env t  in
            desugar_term env uu____26937  in
          let quals1 =
            let uu____26941 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____26941
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____26950 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____26950;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
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
                let uu____26964 =
                  let uu____26973 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____26973]  in
                let uu____26992 =
                  let uu____26995 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____26995
                   in
                FStar_Syntax_Util.arrow uu____26964 uu____26992
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
            let uu____27050 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27050 with
            | FStar_Pervasives_Native.None  ->
                let uu____27053 =
                  let uu____27059 =
                    let uu____27061 =
                      let uu____27063 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____27063 " not found"  in
                    Prims.strcat "Effect name " uu____27061  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27059)  in
                FStar_Errors.raise_error uu____27053
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27071 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27089 =
                  let uu____27092 =
                    let uu____27093 = desugar_term env t  in
                    ([], uu____27093)  in
                  FStar_Pervasives_Native.Some uu____27092  in
                (uu____27089, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27106 =
                  let uu____27109 =
                    let uu____27110 = desugar_term env wp  in
                    ([], uu____27110)  in
                  FStar_Pervasives_Native.Some uu____27109  in
                let uu____27117 =
                  let uu____27120 =
                    let uu____27121 = desugar_term env t  in
                    ([], uu____27121)  in
                  FStar_Pervasives_Native.Some uu____27120  in
                (uu____27106, uu____27117)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27133 =
                  let uu____27136 =
                    let uu____27137 = desugar_term env t  in
                    ([], uu____27137)  in
                  FStar_Pervasives_Native.Some uu____27136  in
                (FStar_Pervasives_Native.None, uu____27133)
             in
          (match uu____27071 with
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
            let uu____27171 =
              let uu____27172 =
                let uu____27179 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27179, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27172  in
            {
              FStar_Syntax_Syntax.sigel = uu____27171;
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
      let uu____27206 =
        FStar_List.fold_left
          (fun uu____27226  ->
             fun d  ->
               match uu____27226 with
               | (env1,sigelts) ->
                   let uu____27246 = desugar_decl env1 d  in
                   (match uu____27246 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27206 with
      | (env1,sigelts) ->
          let rec forward acc uu___277_27291 =
            match uu___277_27291 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27305,FStar_Syntax_Syntax.Sig_let uu____27306) ->
                     let uu____27319 =
                       let uu____27322 =
                         let uu___316_27323 = se2  in
                         let uu____27324 =
                           let uu____27327 =
                             FStar_List.filter
                               (fun uu___276_27341  ->
                                  match uu___276_27341 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27346;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27347;_},uu____27348);
                                      FStar_Syntax_Syntax.pos = uu____27349;
                                      FStar_Syntax_Syntax.vars = uu____27350;_}
                                      when
                                      let uu____27377 =
                                        let uu____27379 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27379
                                         in
                                      uu____27377 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27383 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27327
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___316_27323.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___316_27323.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___316_27323.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___316_27323.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27324
                         }  in
                       uu____27322 :: se1 :: acc  in
                     forward uu____27319 sigelts1
                 | uu____27389 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27397 = forward [] sigelts  in (env1, uu____27397)
  
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
          | (FStar_Pervasives_Native.None ,uu____27462) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27466;
               FStar_Syntax_Syntax.exports = uu____27467;
               FStar_Syntax_Syntax.is_interface = uu____27468;_},FStar_Parser_AST.Module
             (current_lid,uu____27470)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27479) ->
              let uu____27482 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27482
           in
        let uu____27487 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27529 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27529, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27551 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27551, mname, decls, false)
           in
        match uu____27487 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27593 = desugar_decls env2 decls  in
            (match uu____27593 with
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
          let uu____27661 =
            (FStar_Options.interactive ()) &&
              (let uu____27664 =
                 let uu____27666 =
                   let uu____27668 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27668  in
                 FStar_Util.get_file_extension uu____27666  in
               FStar_List.mem uu____27664 ["fsti"; "fsi"])
             in
          if uu____27661 then as_interface m else m  in
        let uu____27682 = desugar_modul_common curmod env m1  in
        match uu____27682 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27704 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27704, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27726 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27726 with
      | (env1,modul,pop_when_done) ->
          let uu____27743 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27743 with
           | (env2,modul1) ->
               ((let uu____27755 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27755
                 then
                   let uu____27758 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27758
                 else ());
                (let uu____27763 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27763, modul1))))
  
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
        (fun uu____27817  ->
           let uu____27818 = desugar_modul env modul  in
           match uu____27818 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____27860  ->
           let uu____27861 = desugar_decls env decls  in
           match uu____27861 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____27916  ->
             let uu____27917 = desugar_partial_modul modul env a_modul  in
             match uu____27917 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28016 ->
                  let t =
                    let uu____28026 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28026  in
                  let uu____28039 =
                    let uu____28040 = FStar_Syntax_Subst.compress t  in
                    uu____28040.FStar_Syntax_Syntax.n  in
                  (match uu____28039 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28052,uu____28053)
                       -> bs1
                   | uu____28078 -> failwith "Impossible")
               in
            let uu____28088 =
              let uu____28095 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28095
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28088 with
            | (binders,uu____28097,binders_opening) ->
                let erase_term t =
                  let uu____28105 =
                    let uu____28106 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28106  in
                  FStar_Syntax_Subst.close binders uu____28105  in
                let erase_tscheme uu____28124 =
                  match uu____28124 with
                  | (us,t) ->
                      let t1 =
                        let uu____28144 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28144 t  in
                      let uu____28147 =
                        let uu____28148 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28148  in
                      ([], uu____28147)
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
                    | uu____28171 ->
                        let bs =
                          let uu____28181 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28181  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28221 =
                          let uu____28222 =
                            let uu____28225 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28225  in
                          uu____28222.FStar_Syntax_Syntax.n  in
                        (match uu____28221 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28227,uu____28228) -> bs1
                         | uu____28253 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28261 =
                      let uu____28262 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28262  in
                    FStar_Syntax_Subst.close binders uu____28261  in
                  let uu___317_28263 = action  in
                  let uu____28264 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28265 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___317_28263.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___317_28263.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28264;
                    FStar_Syntax_Syntax.action_typ = uu____28265
                  }  in
                let uu___318_28266 = ed  in
                let uu____28267 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28268 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28269 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28270 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28271 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28272 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28273 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28274 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28275 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28276 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28277 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28278 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28279 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28280 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28281 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28282 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___318_28266.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___318_28266.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28267;
                  FStar_Syntax_Syntax.signature = uu____28268;
                  FStar_Syntax_Syntax.ret_wp = uu____28269;
                  FStar_Syntax_Syntax.bind_wp = uu____28270;
                  FStar_Syntax_Syntax.if_then_else = uu____28271;
                  FStar_Syntax_Syntax.ite_wp = uu____28272;
                  FStar_Syntax_Syntax.stronger = uu____28273;
                  FStar_Syntax_Syntax.close_wp = uu____28274;
                  FStar_Syntax_Syntax.assert_p = uu____28275;
                  FStar_Syntax_Syntax.assume_p = uu____28276;
                  FStar_Syntax_Syntax.null_wp = uu____28277;
                  FStar_Syntax_Syntax.trivial = uu____28278;
                  FStar_Syntax_Syntax.repr = uu____28279;
                  FStar_Syntax_Syntax.return_repr = uu____28280;
                  FStar_Syntax_Syntax.bind_repr = uu____28281;
                  FStar_Syntax_Syntax.actions = uu____28282;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___318_28266.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___319_28298 = se  in
                  let uu____28299 =
                    let uu____28300 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28300  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28299;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___319_28298.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___319_28298.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___319_28298.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___319_28298.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___320_28304 = se  in
                  let uu____28305 =
                    let uu____28306 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28306
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28305;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___320_28304.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___320_28304.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___320_28304.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___320_28304.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28308 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28309 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28309 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28326 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28326
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28328 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28328)
  