open Prims
let desugar_disjunctive_pattern :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list
  =
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
let trans_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___82_58  ->
    match uu___82_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___83_76  ->
        match uu___83_76 with
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___84_83  ->
    match uu___84_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___85_92  ->
    match uu___85_92 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____95 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____99 .
    FStar_Parser_AST.imp ->
      'Auu____99 ->
        ('Auu____99,FStar_Syntax_Syntax.arg_qualifier
                      FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____119 .
    FStar_Parser_AST.imp ->
      'Auu____119 ->
        ('Auu____119,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____136 -> (t, FStar_Pervasives_Native.None)
  
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____151 -> true
            | uu____156 -> false))
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____161 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____166  in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____170 =
      let uu____171 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____171  in
    FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____178 =
        let uu____179 = unparen t  in uu____179.FStar_Parser_AST.tm  in
      match uu____178 with
      | FStar_Parser_AST.Name l ->
          let uu____181 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____181 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____187) ->
          let uu____200 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____206,uu____207) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "nope"
      | FStar_Parser_AST.Ascribed (t1,uu____210,uu____211) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____216,t1) -> is_comp_type env t1
      | uu____218 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____228 =
          let uu____231 =
            let uu____232 =
              let uu____237 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____237, r)  in
            FStar_Ident.mk_ident uu____232  in
          [uu____231]  in
        FStar_All.pipe_right uu____228 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____245 .
    FStar_ToSyntax_Env.env ->
      Prims.int ->
        'Auu____245 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____273 =
              let uu____274 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____273  in
          let fallback uu____280 =
            match FStar_Ident.text_of_id op with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____283 = FStar_Options.ml_ish ()  in
                if uu____283
                then
                  r FStar_Parser_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____287 -> FStar_Pervasives_Native.None  in
          let uu____288 =
            let uu____295 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_ToSyntax_Env.try_lookup_lid env uu____295  in
          match uu____288 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____307 -> fallback ()
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____323 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____323
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____362 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____366 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____366 with | (env1,uu____378) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____381,term) ->
          let uu____383 = free_type_vars env term  in (env, uu____383)
      | FStar_Parser_AST.TAnnotated (id1,uu____389) ->
          let uu____390 = FStar_ToSyntax_Env.push_bv env id1  in
          (match uu____390 with | (env1,uu____402) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____406 = free_type_vars env t  in (env, uu____406)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____413 =
        let uu____414 = unparen t  in uu____414.FStar_Parser_AST.tm  in
      match uu____413 with
      | FStar_Parser_AST.Labeled uu____417 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____427 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____427 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____440 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____447 -> []
      | FStar_Parser_AST.Uvar uu____448 -> []
      | FStar_Parser_AST.Var uu____449 -> []
      | FStar_Parser_AST.Projector uu____450 -> []
      | FStar_Parser_AST.Discrim uu____455 -> []
      | FStar_Parser_AST.Name uu____456 -> []
      | FStar_Parser_AST.Assign (uu____457,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____460) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____466) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____471,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "nope"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____489,ts) ->
          FStar_List.collect
            (fun uu____510  ->
               match uu____510 with | (t1,uu____518) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____519,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____527) ->
          let uu____528 = free_type_vars env t1  in
          let uu____531 = free_type_vars env t2  in
          FStar_List.append uu____528 uu____531
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____536 = free_type_vars_b env b  in
          (match uu____536 with
           | (env1,f) ->
               let uu____551 = free_type_vars env1 t1  in
               FStar_List.append f uu____551)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____560 =
            FStar_List.fold_left
              (fun uu____580  ->
                 fun binder  ->
                   match uu____580 with
                   | (env1,free) ->
                       let uu____600 = free_type_vars_b env1 binder  in
                       (match uu____600 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____560 with
           | (env1,free) ->
               let uu____631 = free_type_vars env1 body  in
               FStar_List.append free uu____631)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____640 =
            FStar_List.fold_left
              (fun uu____660  ->
                 fun binder  ->
                   match uu____660 with
                   | (env1,free) ->
                       let uu____680 = free_type_vars_b env1 binder  in
                       (match uu____680 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____640 with
           | (env1,free) ->
               let uu____711 = free_type_vars env1 body  in
               FStar_List.append free uu____711)
      | FStar_Parser_AST.Project (t1,uu____715) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____719 -> []
      | FStar_Parser_AST.Let uu____726 -> []
      | FStar_Parser_AST.LetOpen uu____747 -> []
      | FStar_Parser_AST.If uu____752 -> []
      | FStar_Parser_AST.QForall uu____759 -> []
      | FStar_Parser_AST.QExists uu____772 -> []
      | FStar_Parser_AST.Record uu____785 -> []
      | FStar_Parser_AST.Match uu____798 -> []
      | FStar_Parser_AST.TryWith uu____813 -> []
      | FStar_Parser_AST.Bind uu____828 -> []
      | FStar_Parser_AST.Seq uu____835 -> []

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____882 =
        let uu____883 = unparen t1  in uu____883.FStar_Parser_AST.tm  in
      match uu____882 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____925 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____945 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____945  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____963 =
                     let uu____964 =
                       let uu____969 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____969)  in
                     FStar_Parser_AST.TAnnotated uu____964  in
                   FStar_Parser_AST.mk_binder uu____963 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let close_fun :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____982 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____982  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1000 =
                     let uu____1001 =
                       let uu____1006 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1006)  in
                     FStar_Parser_AST.TAnnotated uu____1001  in
                   FStar_Parser_AST.mk_binder uu____1000
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1008 =
             let uu____1009 = unparen t  in uu____1009.FStar_Parser_AST.tm
              in
           match uu____1008 with
           | FStar_Parser_AST.Product uu____1010 -> t
           | uu____1017 ->
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
  
let rec uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1049 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1055,uu____1056) -> true
    | FStar_Parser_AST.PatVar (uu____1061,uu____1062) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1068) -> is_var_pattern p1
    | uu____1069 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1074) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1075;
           FStar_Parser_AST.prange = uu____1076;_},uu____1077)
        -> true
    | uu____1088 -> false
  
let replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1092 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1132 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1132 with
             | (name,args,uu____1163) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1189);
               FStar_Parser_AST.prange = uu____1190;_},args)
            when is_top_level1 ->
            let uu____1200 =
              let uu____1205 = FStar_ToSyntax_Env.qualify env id1  in
              FStar_Util.Inr uu____1205  in
            (uu____1200, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1215);
               FStar_Parser_AST.prange = uu____1216;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1234 -> failwith "Not an app pattern"
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1272 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1273,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1276 -> acc
      | FStar_Parser_AST.PatTvar uu____1277 -> acc
      | FStar_Parser_AST.PatOp uu____1284 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1292) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1301) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1316 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1316
      | FStar_Parser_AST.PatAscribed (pat,uu____1324) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then (Prims.parse_int "0")
           else (Prims.parse_int "1"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1362 -> false
  
let __proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1390 -> false
  
let __proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___86_1416  ->
    match uu___86_1416 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1423 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun imp  ->
      fun uu___87_1448  ->
        match uu___87_1448 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1464 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1464, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1469 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1469 with
             | (env1,a1) ->
                 (((let uu___111_1489 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1489.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1489.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_ToSyntax_Env.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple4 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1514  ->
    match uu____1514 with
    | (attrs,n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs
        }
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1579 =
        let uu____1594 =
          let uu____1595 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1595  in
        let uu____1596 =
          let uu____1605 =
            let uu____1612 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1612)  in
          [uu____1605]  in
        (uu____1594, uu____1596)  in
      FStar_Syntax_Syntax.Tm_app uu____1579  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1645 =
        let uu____1660 =
          let uu____1661 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1661  in
        let uu____1662 =
          let uu____1671 =
            let uu____1678 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1678)  in
          [uu____1671]  in
        (uu____1660, uu____1662)  in
      FStar_Syntax_Syntax.Tm_app uu____1645  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1721 =
            let uu____1736 =
              let uu____1737 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1737  in
            let uu____1738 =
              let uu____1747 =
                let uu____1754 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1754)  in
              let uu____1757 =
                let uu____1766 =
                  let uu____1773 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1773)  in
                [uu____1766]  in
              uu____1747 :: uu____1757  in
            (uu____1736, uu____1738)  in
          FStar_Syntax_Syntax.Tm_app uu____1721  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___88_1804  ->
    match uu___88_1804 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1805 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1813 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1813)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1828 =
      let uu____1829 = unparen t  in uu____1829.FStar_Parser_AST.tm  in
    match uu____1828 with
    | FStar_Parser_AST.Wild  ->
        let uu____1834 =
          let uu____1835 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1835  in
        FStar_Util.Inr uu____1834
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1846)) ->
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
             let uu____1912 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1912
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1923 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1923
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1934 =
               let uu____1939 =
                 let uu____1940 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1940
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1939)
                in
             FStar_Errors.raise_error uu____1934 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1945 ->
        let rec aux t1 univargs =
          let uu____1975 =
            let uu____1976 = unparen t1  in uu____1976.FStar_Parser_AST.tm
             in
          match uu____1975 with
          | FStar_Parser_AST.App (t2,targ,uu____1983) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2007  ->
                     match uu___89_2007 with
                     | FStar_Util.Inr uu____2012 -> true
                     | uu____2013 -> false) univargs
              then
                let uu____2018 =
                  let uu____2019 =
                    FStar_List.map
                      (fun uu___90_2028  ->
                         match uu___90_2028 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2019  in
                FStar_Util.Inr uu____2018
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2045  ->
                        match uu___91_2045 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2051 -> failwith "impossible")
                     univargs
                    in
                 let uu____2052 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2052)
          | uu____2058 ->
              let uu____2059 =
                let uu____2064 =
                  let uu____2065 =
                    let uu____2066 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2066 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2065  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2064)  in
              FStar_Errors.raise_error uu____2059 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2075 ->
        let uu____2076 =
          let uu____2081 =
            let uu____2082 =
              let uu____2083 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2083 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2082  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2081)  in
        FStar_Errors.raise_error uu____2076 t.FStar_Parser_AST.range
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2102 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2102) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2127 = FStar_List.hd fields  in
        match uu____2127 with
        | (f,uu____2137) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2147 =
                match uu____2147 with
                | (f',uu____2153) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2155 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record
                         in
                      if uu____2155
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____2159 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2159);
              (match () with | () -> record)))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 r =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2376 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2383 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2384 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2386,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2427  ->
                          match uu____2427 with
                          | (p3,uu____2437) ->
                              let uu____2438 =
                                let uu____2439 =
                                  let uu____2442 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2442 out  in
                                FStar_Util.set_is_empty uu____2439  in
                              if uu____2438
                              then
                                let uu____2447 = pat_vars p3  in
                                FStar_Util.set_union out uu____2447
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2454) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2455) -> ()
         | (true ,uu____2462) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____2497 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2497 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2511 ->
               let uu____2514 = push_bv_maybe_mut e x  in
               (match uu____2514 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2601 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2617 =
                 let uu____2618 =
                   let uu____2619 =
                     let uu____2626 =
                       let uu____2627 =
                         let uu____2632 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2632, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2627  in
                     (uu____2626, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2619  in
                 {
                   FStar_Parser_AST.pat = uu____2618;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2617
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2637 = aux loc env1 p2  in
               (match uu____2637 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2691 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2696 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2696.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2696.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2691.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2698 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2703 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2703.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2703.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2698.FStar_Syntax_Syntax.p)
                          }
                      | uu____2704 when top -> p4
                      | uu____2705 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2708 =
                      match binder with
                      | LetBinder uu____2721 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2735 = close_fun env1 t  in
                            desugar_term env1 uu____2735  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2737 -> true)
                           then
                             (let uu____2738 =
                                let uu____2743 =
                                  let uu____2744 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2745 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2746 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2744 uu____2745 uu____2746
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2743)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2738)
                           else ();
                           (let uu____2748 = annot_pat_var p3 t1  in
                            (uu____2748,
                              (LocalBinder
                                 ((let uu___116_2754 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2754.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2754.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2708 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2776 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2776, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2787 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2787, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2808 = resolvex loc env1 x  in
               (match uu____2808 with
                | (loc1,env2,xbv) ->
                    let uu____2830 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2830, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2851 = resolvex loc env1 x  in
               (match uu____2851 with
                | (loc1,env2,xbv) ->
                    let uu____2873 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2873, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2885 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2885, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2909;_},args)
               ->
               let uu____2915 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2956  ->
                        match uu____2956 with
                        | (loc1,env2,args1) ->
                            let uu____3004 = aux loc1 env2 arg  in
                            (match uu____3004 with
                             | (loc2,env3,uu____3033,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2915 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____3103 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3103, false))
           | FStar_Parser_AST.PatApp uu____3120 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3142 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3175  ->
                        match uu____3175 with
                        | (loc1,env2,pats1) ->
                            let uu____3207 = aux loc1 env2 pat  in
                            (match uu____3207 with
                             | (loc2,env3,uu____3232,pat1,uu____3234) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3142 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3277 =
                        let uu____3280 =
                          let uu____3285 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3285  in
                        let uu____3286 =
                          let uu____3287 =
                            let uu____3300 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3300, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3287  in
                        FStar_All.pipe_left uu____3280 uu____3286  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3332 =
                               let uu____3333 =
                                 let uu____3346 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3346, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3333  in
                             FStar_All.pipe_left (pos_r r) uu____3332) pats1
                        uu____3277
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3390 =
                 FStar_List.fold_left
                   (fun uu____3430  ->
                      fun p2  ->
                        match uu____3430 with
                        | (loc1,env2,pats) ->
                            let uu____3479 = aux loc1 env2 p2  in
                            (match uu____3479 with
                             | (loc2,env3,uu____3508,pat,uu____3510) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3390 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____3605 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____3605 with
                     | (constr,uu____3627) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3630 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3632 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3632, false)))
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
                      (fun uu____3703  ->
                         match uu____3703 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3733  ->
                         match uu____3733 with
                         | (f,uu____3739) ->
                             let uu____3740 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3766  ->
                                       match uu____3766 with
                                       | (g,uu____3772) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3740 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3777,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3784 =
                   let uu____3785 =
                     let uu____3792 =
                       let uu____3793 =
                         let uu____3794 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3794  in
                       FStar_Parser_AST.mk_pattern uu____3793
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3792, args)  in
                   FStar_Parser_AST.PatApp uu____3785  in
                 FStar_Parser_AST.mk_pattern uu____3784
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3797 = aux loc env1 app  in
               (match uu____3797 with
                | (env2,e,b,p2,uu____3826) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3854 =
                            let uu____3855 =
                              let uu____3868 =
                                let uu___117_3869 = fv  in
                                let uu____3870 =
                                  let uu____3873 =
                                    let uu____3874 =
                                      let uu____3881 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3881)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3874
                                     in
                                  FStar_Pervasives_Native.Some uu____3873  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3869.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3869.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3870
                                }  in
                              (uu____3868, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3855  in
                          FStar_All.pipe_left pos uu____3854
                      | uu____3908 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3958 = aux' true loc env1 p2  in
               (match uu____3958 with
                | (loc1,env2,var,p3,uu____3985) ->
                    let uu____3990 =
                      FStar_List.fold_left
                        (fun uu____4022  ->
                           fun p4  ->
                             match uu____4022 with
                             | (loc2,env3,ps1) ->
                                 let uu____4055 = aux' true loc2 env3 p4  in
                                 (match uu____4055 with
                                  | (loc3,env4,uu____4080,p5,uu____4082) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3990 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4133 ->
               let uu____4134 = aux' true loc env1 p1  in
               (match uu____4134 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4174 = aux_maybe_or env p  in
         match uu____4174 with
         | (env1,b,pats) ->
             ((let uu____4205 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4205);
              (env1, b, pats)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____4242 =
              let uu____4243 =
                let uu____4248 = FStar_ToSyntax_Env.qualify env x  in
                (uu____4248, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4243  in
            (env, uu____4242, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4268 =
                  let uu____4269 =
                    let uu____4274 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4274, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4269  in
                mklet uu____4268
            | FStar_Parser_AST.PatVar (x,uu____4276) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4282);
                   FStar_Parser_AST.prange = uu____4283;_},t)
                ->
                let uu____4289 =
                  let uu____4290 =
                    let uu____4295 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____4296 = desugar_term env t  in
                    (uu____4295, uu____4296)  in
                  LetBinder uu____4290  in
                (env, uu____4289, [])
            | uu____4299 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4309 = desugar_data_pat env p is_mut  in
             match uu____4309 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4338;
                       FStar_Syntax_Syntax.p = uu____4339;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4344;
                       FStar_Syntax_Syntax.p = uu____4345;_}::[] -> []
                   | uu____4350 -> p1  in
                 (env1, binder, p2))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun uu____4357  ->
    fun env  ->
      fun pat  ->
        let uu____4360 = desugar_data_pat env pat false  in
        match uu____4360 with | (env1,uu____4376,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and desugar_machine_integer :
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun repr  ->
      fun uu____4394  ->
        fun range  ->
          match uu____4394 with
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
              ((let uu____4404 =
                  let uu____4405 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4405  in
                if uu____4404
                then
                  let uu____4406 =
                    let uu____4411 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4411)  in
                  FStar_Errors.log_issue range uu____4406
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
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range
                   in
                let lid1 =
                  let uu____4419 = FStar_ToSyntax_Env.try_lookup_lid env lid
                     in
                  match uu____4419 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4429) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4439 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4439 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4440 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4440.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4440.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4441 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4448 =
                        let uu____4453 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4453)
                         in
                      FStar_Errors.raise_error uu____4448 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4469 =
                  let uu____4472 =
                    let uu____4473 =
                      let uu____4488 =
                        let uu____4497 =
                          let uu____4504 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4504)  in
                        [uu____4497]  in
                      (lid1, uu____4488)  in
                    FStar_Syntax_Syntax.Tm_app uu____4473  in
                  FStar_Syntax_Syntax.mk uu____4472  in
                uu____4469 FStar_Pervasives_Native.None range))

and desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____4543 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid_with_attributes
                  else
                    FStar_ToSyntax_Env.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4543 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4589;
                              FStar_Syntax_Syntax.vars = uu____4590;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4613 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4613 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4621 =
                                 let uu____4622 =
                                   let uu____4625 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4625  in
                                 uu____4622.FStar_Syntax_Syntax.n  in
                               match uu____4621 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4641))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4642 -> msg
                             else msg  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4646 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4646 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4647 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4652 =
                      let uu____4653 =
                        let uu____4660 = mk_ref_read tm1  in
                        (uu____4660,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4653  in
                    FStar_All.pipe_left mk1 uu____4652
                  else tm1))

and desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4676 =
          let uu____4677 = unparen t  in uu____4677.FStar_Parser_AST.tm  in
        match uu____4676 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4678; FStar_Ident.ident = uu____4679;
              FStar_Ident.nsstr = uu____4680; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4683 ->
            let uu____4684 =
              let uu____4689 =
                let uu____4690 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4690  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4689)  in
            FStar_Errors.raise_error uu____4684 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___119_4710 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4710.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4710.FStar_Syntax_Syntax.vars)
          }  in
        let uu____4713 =
          let uu____4714 = unparen top  in uu____4714.FStar_Parser_AST.tm  in
        match uu____4713 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4715 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4766::uu____4767::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4771 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4771 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4784;_},t1::t2::[])
                  ->
                  let uu____4789 = flatten1 t1  in
                  FStar_List.append uu____4789 [t2]
              | uu____4792 -> [t]  in
            let targs =
              let uu____4796 =
                let uu____4799 = unparen top  in flatten1 uu____4799  in
              FStar_All.pipe_right uu____4796
                (FStar_List.map
                   (fun t  ->
                      let uu____4807 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4807))
               in
            let uu____4808 =
              let uu____4813 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4813
               in
            (match uu____4808 with
             | (tup,uu____4819) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4823 =
              let uu____4826 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4826  in
            FStar_All.pipe_left setpos uu____4823
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4846 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4846 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4878 = desugar_term env t  in
                             (uu____4878, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4892)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4907 =
              let uu___120_4908 = top  in
              let uu____4909 =
                let uu____4910 =
                  let uu____4917 =
                    let uu___121_4918 = top  in
                    let uu____4919 =
                      let uu____4920 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4920  in
                    {
                      FStar_Parser_AST.tm = uu____4919;
                      FStar_Parser_AST.range =
                        (uu___121_4918.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4918.FStar_Parser_AST.level)
                    }  in
                  (uu____4917, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4910  in
              {
                FStar_Parser_AST.tm = uu____4909;
                FStar_Parser_AST.range =
                  (uu___120_4908.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4908.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4907
        | FStar_Parser_AST.Construct (n1,(a,uu____4923)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4939 =
                let uu___122_4940 = top  in
                let uu____4941 =
                  let uu____4942 =
                    let uu____4949 =
                      let uu___123_4950 = top  in
                      let uu____4951 =
                        let uu____4952 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4952  in
                      {
                        FStar_Parser_AST.tm = uu____4951;
                        FStar_Parser_AST.range =
                          (uu___123_4950.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4950.FStar_Parser_AST.level)
                      }  in
                    (uu____4949, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4942  in
                {
                  FStar_Parser_AST.tm = uu____4941;
                  FStar_Parser_AST.range =
                    (uu___122_4940.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4940.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4939))
        | FStar_Parser_AST.Construct (n1,(a,uu____4955)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4970 =
              let uu___124_4971 = top  in
              let uu____4972 =
                let uu____4973 =
                  let uu____4980 =
                    let uu___125_4981 = top  in
                    let uu____4982 =
                      let uu____4983 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4983  in
                    {
                      FStar_Parser_AST.tm = uu____4982;
                      FStar_Parser_AST.range =
                        (uu___125_4981.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4981.FStar_Parser_AST.level)
                    }  in
                  (uu____4980, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4973  in
              {
                FStar_Parser_AST.tm = uu____4972;
                FStar_Parser_AST.range =
                  (uu___124_4971.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4971.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4970
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4984; FStar_Ident.ident = uu____4985;
              FStar_Ident.nsstr = uu____4986; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4989; FStar_Ident.ident = uu____4990;
              FStar_Ident.nsstr = uu____4991; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4994; FStar_Ident.ident = uu____4995;
               FStar_Ident.nsstr = uu____4996; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5014 =
              let uu____5015 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____5015  in
            mk1 uu____5014
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5016; FStar_Ident.ident = uu____5017;
              FStar_Ident.nsstr = uu____5018; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5021; FStar_Ident.ident = uu____5022;
              FStar_Ident.nsstr = uu____5023; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5026; FStar_Ident.ident = uu____5027;
              FStar_Ident.nsstr = uu____5028; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5033;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5035 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____5035 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5040 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5040))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____5044 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____5044 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssignToImmutableValues,
                        "Can only assign to mutable values")
                      top.FStar_Parser_AST.range
                  else ();
                  mk_ref_assign t1 t21 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5071 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____5071 with
                | FStar_Pervasives_Native.Some uu____5080 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5085 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____5085 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5099 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5112 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5112
              | uu____5113 ->
                  let uu____5120 =
                    let uu____5125 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5125)  in
                  FStar_Errors.raise_error uu____5120
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5128 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____5128 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5131 =
                    let uu____5136 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5136)
                     in
                  FStar_Errors.raise_error uu____5131
                    top.FStar_Parser_AST.range
              | uu____5137 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5156 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____5156 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5160 =
                    let uu____5167 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____5167, true)  in
                  (match uu____5160 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5182 ->
                            let uu____5189 =
                              FStar_Util.take
                                (fun uu____5213  ->
                                   match uu____5213 with
                                   | (uu____5218,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____5189 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5282  ->
                                        match uu____5282 with
                                        | (t,imp) ->
                                            let te = desugar_term env t  in
                                            arg_withimp_e imp te) args1
                                    in
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let app =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 if is_data
                                 then
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (app,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Data_app)))
                                 else app)))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____5329 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____5329 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5336 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5343 =
              FStar_List.fold_left
                (fun uu____5388  ->
                   fun b  ->
                     match uu____5388 with
                     | (env1,tparams,typs) ->
                         let uu____5445 = desugar_binder env1 b  in
                         (match uu____5445 with
                          | (xopt,t1) ->
                              let uu____5474 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5483 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5483)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____5474 with
                               | (env2,x) ->
                                   let uu____5503 =
                                     let uu____5506 =
                                       let uu____5509 =
                                         let uu____5510 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5510
                                          in
                                       [uu____5509]  in
                                     FStar_List.append typs uu____5506  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5536 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5536.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5536.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5503)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5343 with
             | (env1,uu____5560,targs) ->
                 let uu____5582 =
                   let uu____5587 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5587
                    in
                 (match uu____5582 with
                  | (tup,uu____5593) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5604 = uncurry binders t  in
            (match uu____5604 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5636 =
                   match uu___92_5636 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5650 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5650
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5672 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5672 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5687 = desugar_binder env b  in
            (match uu____5687 with
             | (FStar_Pervasives_Native.None ,uu____5694) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5704 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5704 with
                  | ((x,uu____5710),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5717 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5717))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5737 =
              FStar_List.fold_left
                (fun uu____5757  ->
                   fun pat  ->
                     match uu____5757 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5783,t) ->
                              let uu____5785 =
                                let uu____5788 = free_type_vars env1 t  in
                                FStar_List.append uu____5788 ftvs  in
                              (env1, uu____5785)
                          | uu____5793 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5737 with
             | (uu____5798,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5810 =
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
                   FStar_List.append uu____5810 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5851 =
                   match uu___93_5851 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5889 =
                                 let uu____5890 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5890
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5889 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5943 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5943
                   | p::rest ->
                       let uu____5954 = desugar_binding_pat env1 p  in
                       (match uu____5954 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5978 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5983 =
                              match b with
                              | LetBinder uu____6016 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6066) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6102 =
                                          let uu____6107 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6107, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6102
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6143,uu____6144) ->
                                             let tup2 =
                                               let uu____6146 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6146
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6150 =
                                                 let uu____6153 =
                                                   let uu____6154 =
                                                     let uu____6169 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6172 =
                                                       let uu____6175 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6176 =
                                                         let uu____6179 =
                                                           let uu____6180 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6180
                                                            in
                                                         [uu____6179]  in
                                                       uu____6175 ::
                                                         uu____6176
                                                        in
                                                     (uu____6169, uu____6172)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6154
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6153
                                                  in
                                               uu____6150
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6191 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6191
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6222,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6224,pats)) ->
                                             let tupn =
                                               let uu____6263 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6263
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6273 =
                                                 let uu____6274 =
                                                   let uu____6289 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6292 =
                                                     let uu____6301 =
                                                       let uu____6310 =
                                                         let uu____6311 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6311
                                                          in
                                                       [uu____6310]  in
                                                     FStar_List.append args
                                                       uu____6301
                                                      in
                                                   (uu____6289, uu____6292)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6274
                                                  in
                                               mk1 uu____6273  in
                                             let p2 =
                                               let uu____6331 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6331
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6366 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5983 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6433,uu____6434,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6448 =
                let uu____6449 = unparen e  in uu____6449.FStar_Parser_AST.tm
                 in
              match uu____6448 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6455 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6459 ->
            let rec aux args e =
              let uu____6491 =
                let uu____6492 = unparen e  in uu____6492.FStar_Parser_AST.tm
                 in
              match uu____6491 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6505 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6505  in
                  aux (arg :: args) e1
              | uu____6518 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let tac_bind_lid =
              FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Effect"; "bind"]
                x.FStar_Ident.idRange
               in
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
            let uu____6546 =
              FStar_ToSyntax_Env.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6546 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6551 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6551
             | uu____6552 ->
                 let uu____6555 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6555)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6558 =
              let uu____6559 =
                let uu____6566 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [(FStar_Pervasives_Native.None,
                               ((FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   t1.FStar_Parser_AST.range), t1))], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____6566,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6559  in
            mk1 uu____6558
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____6618 =
              let uu____6623 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____6623 then desugar_typ else desugar_term  in
            uu____6618 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6666 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6791  ->
                        match uu____6791 with
                        | (attr_opt,(p,def)) ->
                            let uu____6843 = is_app_pattern p  in
                            if uu____6843
                            then
                              let uu____6868 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6868, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6932 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6932, def1)
                               | uu____6965 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6997);
                                           FStar_Parser_AST.prange =
                                             uu____6998;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____7028 =
                                            let uu____7043 =
                                              let uu____7048 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7048  in
                                            (uu____7043, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____7028, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7103) ->
                                        if top_level
                                        then
                                          let uu____7132 =
                                            let uu____7147 =
                                              let uu____7152 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7152  in
                                            (uu____7147, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7132, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7206 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7231 =
                FStar_List.fold_left
                  (fun uu____7298  ->
                     fun uu____7299  ->
                       match (uu____7298, uu____7299) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7395,uu____7396),uu____7397))
                           ->
                           let uu____7490 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7516 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____7516 with
                                  | (env2,xx) ->
                                      let uu____7535 =
                                        let uu____7538 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7538 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7535))
                             | FStar_Util.Inr l ->
                                 let uu____7546 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7546, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7490 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7231 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7678 =
                    match uu____7678 with
                    | (attrs_opt,(uu____7708,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7760 = is_comp_type env1 t  in
                                if uu____7760
                                then
                                  ((let uu____7762 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7772 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7772))
                                       in
                                    match uu____7762 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7775 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7777 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7777))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7775
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7781 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7781 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7785 ->
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
                              let uu____7800 =
                                let uu____7801 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7801
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7800
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
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____7855 =
                    let uu____7856 =
                      let uu____7869 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7869)  in
                    FStar_Syntax_Syntax.Tm_let uu____7856  in
                  FStar_All.pipe_left mk1 uu____7855
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let is_mutable = qual = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____7923 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7923 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7950 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7950
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7970) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7973;
                              FStar_Syntax_Syntax.p = uu____7974;_}::[] ->
                              body1
                          | uu____7979 ->
                              let uu____7982 =
                                let uu____7985 =
                                  let uu____7986 =
                                    let uu____8009 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____8010 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____8009, uu____8010)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7986  in
                                FStar_Syntax_Syntax.mk uu____7985  in
                              uu____7982 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____8020 =
                          let uu____8021 =
                            let uu____8034 =
                              let uu____8035 =
                                let uu____8036 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____8036]  in
                              FStar_Syntax_Subst.close uu____8035 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8034)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____8021  in
                        FStar_All.pipe_left mk1 uu____8020
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____8064 = FStar_List.hd lbs  in
            (match uu____8064 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8104 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8104
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8113 =
                let uu____8114 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8114  in
              mk1 uu____8113  in
            let uu____8115 =
              let uu____8116 =
                let uu____8139 =
                  let uu____8142 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8142
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8163 =
                  let uu____8178 =
                    let uu____8191 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8194 = desugar_term env t2  in
                    (uu____8191, FStar_Pervasives_Native.None, uu____8194)
                     in
                  let uu____8203 =
                    let uu____8218 =
                      let uu____8231 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8234 = desugar_term env t3  in
                      (uu____8231, FStar_Pervasives_Native.None, uu____8234)
                       in
                    [uu____8218]  in
                  uu____8178 :: uu____8203  in
                (uu____8139, uu____8163)  in
              FStar_Syntax_Syntax.Tm_match uu____8116  in
            mk1 uu____8115
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____8375 =
              match uu____8375 with
              | (pat,wopt,b) ->
                  let uu____8393 = desugar_match_pat env pat  in
                  (match uu____8393 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8414 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8414
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8416 =
              let uu____8417 =
                let uu____8440 = desugar_term env e  in
                let uu____8441 = FStar_List.collect desugar_branch branches
                   in
                (uu____8440, uu____8441)  in
              FStar_Syntax_Syntax.Tm_match uu____8417  in
            FStar_All.pipe_left mk1 uu____8416
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8470 = is_comp_type env t  in
              if uu____8470
              then
                let uu____8477 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8477
              else
                (let uu____8483 = desugar_term env t  in
                 FStar_Util.Inl uu____8483)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8489 =
              let uu____8490 =
                let uu____8517 = desugar_term env e  in
                (uu____8517, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8490  in
            FStar_All.pipe_left mk1 uu____8489
        | FStar_Parser_AST.Record (uu____8542,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8579 = FStar_List.hd fields  in
              match uu____8579 with | (f,uu____8591) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8633  ->
                        match uu____8633 with
                        | (g,uu____8639) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8645,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8659 =
                         let uu____8664 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8664)
                          in
                       FStar_Errors.raise_error uu____8659
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
                   [record.FStar_ToSyntax_Env.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8672 =
                    let uu____8683 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8714  ->
                              match uu____8714 with
                              | (f,uu____8724) ->
                                  let uu____8725 =
                                    let uu____8726 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8726
                                     in
                                  (uu____8725, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8683)  in
                  FStar_Parser_AST.Construct uu____8672
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8744 =
                      let uu____8745 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8745  in
                    FStar_Parser_AST.mk_term uu____8744 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8747 =
                      let uu____8760 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8790  ->
                                match uu____8790 with
                                | (f,uu____8800) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8760)  in
                    FStar_Parser_AST.Record uu____8747  in
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
            let e = desugar_term env recterm1  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8862;
                         FStar_Syntax_Syntax.vars = uu____8863;_},args);
                    FStar_Syntax_Syntax.pos = uu____8865;
                    FStar_Syntax_Syntax.vars = uu____8866;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8894 =
                     let uu____8895 =
                       let uu____8910 =
                         let uu____8911 =
                           let uu____8914 =
                             let uu____8915 =
                               let uu____8922 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8922)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____8915  in
                           FStar_Pervasives_Native.Some uu____8914  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8911
                          in
                       (uu____8910, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____8895  in
                   FStar_All.pipe_left mk1 uu____8894  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8953 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8957 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____8957 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e  in
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
                  let uu____8976 =
                    let uu____8977 =
                      let uu____8992 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8993 =
                        let uu____8996 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8996]  in
                      (uu____8992, uu____8993)  in
                    FStar_Syntax_Syntax.Tm_app uu____8977  in
                  FStar_All.pipe_left mk1 uu____8976))
        | FStar_Parser_AST.NamedTyp (uu____9001,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> failwith "nope"
        | uu____9004 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____9005 ->
            let uu____9006 =
              let uu____9011 =
                let uu____9012 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____9012  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____9011)  in
            FStar_Errors.raise_error uu____9006 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____9013,uu____9014,uu____9015) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____9044,uu____9045,uu____9046) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____9059,uu____9060,uu____9061) ->
            failwith "Not implemented yet"

and not_ascribed : FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____9075 -> false
    | uu____9084 -> true

and is_synth_by_tactic :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____9090 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid  in
          (match uu____9090 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9094 -> false

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____9131  ->
              match uu____9131 with
              | (a,imp) ->
                  let uu____9144 = desugar_term env a  in
                  arg_withimp_e imp uu____9144))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail a err = FStar_Errors.raise_error err r  in
        let is_requires uu____9170 =
          match uu____9170 with
          | (t1,uu____9176) ->
              let uu____9177 =
                let uu____9178 = unparen t1  in
                uu____9178.FStar_Parser_AST.tm  in
              (match uu____9177 with
               | FStar_Parser_AST.Requires uu____9179 -> true
               | uu____9186 -> false)
           in
        let is_ensures uu____9194 =
          match uu____9194 with
          | (t1,uu____9200) ->
              let uu____9201 =
                let uu____9202 = unparen t1  in
                uu____9202.FStar_Parser_AST.tm  in
              (match uu____9201 with
               | FStar_Parser_AST.Ensures uu____9203 -> true
               | uu____9210 -> false)
           in
        let is_app head1 uu____9221 =
          match uu____9221 with
          | (t1,uu____9227) ->
              let uu____9228 =
                let uu____9229 = unparen t1  in
                uu____9229.FStar_Parser_AST.tm  in
              (match uu____9228 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9231;
                      FStar_Parser_AST.level = uu____9232;_},uu____9233,uu____9234)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9235 -> false)
           in
        let is_smt_pat uu____9243 =
          match uu____9243 with
          | (t1,uu____9249) ->
              let uu____9250 =
                let uu____9251 = unparen t1  in
                uu____9251.FStar_Parser_AST.tm  in
              (match uu____9250 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9254);
                             FStar_Parser_AST.range = uu____9255;
                             FStar_Parser_AST.level = uu____9256;_},uu____9257)::uu____9258::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____9297;
                             FStar_Parser_AST.level = uu____9298;_},uu____9299)::uu____9300::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9325 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9353 = head_and_args t1  in
          match uu____9353 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
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
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let thunk_ens_ ens =
                     let wildpat =
                       FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                         ens.FStar_Parser_AST.range
                        in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr
                      in
                   let thunk_ens uu____9447 =
                     match uu____9447 with
                     | (e,i) ->
                         let uu____9458 = thunk_ens_ e  in (uu____9458, i)
                      in
                   let fail_lemma uu____9468 =
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
                     let msg = FStar_String.concat "\n\t" expected_one_of  in
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
                         let uu____9548 =
                           let uu____9555 =
                             let uu____9562 = thunk_ens ens  in
                             [uu____9562; nil_pat]  in
                           req_true :: uu____9555  in
                         unit_tm :: uu____9548
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9609 =
                           let uu____9616 =
                             let uu____9623 = thunk_ens ens  in
                             [uu____9623; nil_pat]  in
                           req :: uu____9616  in
                         unit_tm :: uu____9609
                     | ens::smtpat::[] when
                         (((let uu____9672 = is_requires ens  in
                            Prims.op_Negation uu____9672) &&
                             (let uu____9674 = is_smt_pat ens  in
                              Prims.op_Negation uu____9674))
                            &&
                            (let uu____9676 = is_decreases ens  in
                             Prims.op_Negation uu____9676))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9677 =
                           let uu____9684 =
                             let uu____9691 = thunk_ens ens  in
                             [uu____9691; smtpat]  in
                           req_true :: uu____9684  in
                         unit_tm :: uu____9677
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9738 =
                           let uu____9745 =
                             let uu____9752 = thunk_ens ens  in
                             [uu____9752; nil_pat; dec]  in
                           req_true :: uu____9745  in
                         unit_tm :: uu____9738
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9812 =
                           let uu____9819 =
                             let uu____9826 = thunk_ens ens  in
                             [uu____9826; smtpat; dec]  in
                           req_true :: uu____9819  in
                         unit_tm :: uu____9812
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9886 =
                           let uu____9893 =
                             let uu____9900 = thunk_ens ens  in
                             [uu____9900; nil_pat; dec]  in
                           req :: uu____9893  in
                         unit_tm :: uu____9886
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9960 =
                           let uu____9967 =
                             let uu____9974 = thunk_ens ens  in
                             [uu____9974; smtpat]  in
                           req :: uu____9967  in
                         unit_tm :: uu____9960
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____10039 =
                           let uu____10046 =
                             let uu____10053 = thunk_ens ens  in
                             [uu____10053; dec; smtpat]  in
                           req :: uu____10046  in
                         unit_tm :: uu____10039
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____10115 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10115, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10143 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10143
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10161 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____10161
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____10199 ->
                   let default_effect =
                     let uu____10201 = FStar_Options.ml_ish ()  in
                     if uu____10201
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10204 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10204
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____10228 = pre_process_comp_typ t  in
        match uu____10228 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10277 =
                       let uu____10282 =
                         let uu____10283 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10283
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10282)
                        in
                     fail () uu____10277)
                else Obj.repr ());
             (let is_universe uu____10292 =
                match uu____10292 with
                | (uu____10297,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10299 = FStar_Util.take is_universe args  in
              match uu____10299 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10358  ->
                         match uu____10358 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10365 =
                    let uu____10380 = FStar_List.hd args1  in
                    let uu____10389 = FStar_List.tl args1  in
                    (uu____10380, uu____10389)  in
                  (match uu____10365 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10444 =
                         let is_decrease uu____10480 =
                           match uu____10480 with
                           | (t1,uu____10490) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10500;
                                       FStar_Syntax_Syntax.vars = uu____10501;_},uu____10502::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10533 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10444 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10647  ->
                                      match uu____10647 with
                                      | (t1,uu____10657) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10666,(arg,uu____10668)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10697 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10710 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags1 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else []
                                    in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes  in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then
                                     match rest2 with
                                     | req::ens::(pat,aq)::[] ->
                                         let pat1 =
                                           match pat.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
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
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10850 -> pat  in
                                         let uu____10851 =
                                           let uu____10862 =
                                             let uu____10873 =
                                               let uu____10882 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10882, aq)  in
                                             [uu____10873]  in
                                           ens :: uu____10862  in
                                         req :: uu____10851
                                     | uu____10923 -> rest2
                                   else rest2  in
                                 FStar_Syntax_Syntax.mk_Comp
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_name = eff;
                                     FStar_Syntax_Syntax.result_typ =
                                       result_typ;
                                     FStar_Syntax_Syntax.effect_args = rest3;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags2
                                          decreases_clause)
                                   })))))

and desugar_formula :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____10945 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10962 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10962.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10962.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10996 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10996.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10996.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10996.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____11055 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____11055)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____11068 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____11068 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_11078 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_11078.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_11078.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11100 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11114 =
                     let uu____11117 =
                       let uu____11118 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11118]  in
                     no_annot_abs uu____11117 body2  in
                   FStar_All.pipe_left setpos uu____11114  in
                 let uu____11123 =
                   let uu____11124 =
                     let uu____11139 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11140 =
                       let uu____11143 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11143]  in
                     (uu____11139, uu____11140)  in
                   FStar_Syntax_Syntax.Tm_app uu____11124  in
                 FStar_All.pipe_left mk1 uu____11123)
        | uu____11148 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11220 = q (rest, pats, body)  in
              let uu____11227 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11220 uu____11227
                FStar_Parser_AST.Formula
               in
            let uu____11228 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11228 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11237 -> failwith "impossible"  in
      let uu____11240 =
        let uu____11241 = unparen f  in uu____11241.FStar_Parser_AST.tm  in
      match uu____11240 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11248,uu____11249) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11260,uu____11261) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11292 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11292
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11328 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11328
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "nope"
      | uu____11371 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      let uu____11376 =
        FStar_List.fold_left
          (fun uu____11412  ->
             fun b  ->
               match uu____11412 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11464 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11464.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11464.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11464.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11481 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____11481 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11501 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11501.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11501.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11518 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11376 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11605 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11605)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11610 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11610)
      | FStar_Parser_AST.TVariable x ->
          let uu____11614 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11614)
      | FStar_Parser_AST.NoName t ->
          let uu____11622 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11622)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___94_11655  ->
                  match uu___94_11655 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11656 -> false))
           in
        let quals2 q =
          let uu____11667 =
            (let uu____11670 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____11670) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____11667
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11683 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11683;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
  
let mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_ToSyntax_Env.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____11714 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11744  ->
                        match uu____11744 with
                        | (x,uu____11752) ->
                            let uu____11753 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11753 with
                             | (field_name,uu____11761) ->
                                 let only_decl =
                                   ((let uu____11765 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11765)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11767 =
                                        let uu____11768 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____11768.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11767)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11782 =
                                       FStar_List.filter
                                         (fun uu___95_11786  ->
                                            match uu___95_11786 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11787 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11782
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11800  ->
                                             match uu___96_11800 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11801 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11809 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11809
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11814 =
                                        let uu____11819 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11819  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11814;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = []
                                      }  in
                                    let impl =
                                      let uu____11823 =
                                        let uu____11824 =
                                          let uu____11831 =
                                            let uu____11834 =
                                              let uu____11835 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11835
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11834]  in
                                          ((false, [lb]), uu____11831)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11824
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11823;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11714 FStar_List.flatten
  
let mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11879,t,uu____11881,n1,uu____11883) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11888 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11888 with
             | (formals,uu____11904) ->
                 (match formals with
                  | [] -> []
                  | uu____11927 ->
                      let filter_records uu___97_11939 =
                        match uu___97_11939 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11942,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11954 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11956 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11956 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11966 = FStar_Util.first_N n1 formals  in
                      (match uu____11966 with
                       | (uu____11989,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____12015 -> []
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____12065 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____12065
                    then
                      let uu____12068 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____12068
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____12071 =
                      let uu____12076 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____12076  in
                    let uu____12077 =
                      let uu____12080 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____12080  in
                    let uu____12083 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____12071;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____12077;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____12083;
                      FStar_Syntax_Syntax.lbattrs = []
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
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___98_12130 =
            match uu___98_12130 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12132,uu____12133) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12143,uu____12144,uu____12145) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12155,uu____12156,uu____12157) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12187,uu____12188,uu____12189) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12231) ->
                let uu____12232 =
                  let uu____12233 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12233  in
                FStar_Parser_AST.mk_term uu____12232 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12235 =
                  let uu____12236 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12236  in
                FStar_Parser_AST.mk_term uu____12235 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12238) ->
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
              | uu____12261 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12267 =
                     let uu____12268 =
                       let uu____12275 = binder_to_term b  in
                       (out, uu____12275, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12268  in
                   FStar_Parser_AST.mk_term uu____12267
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12285 =
            match uu___99_12285 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12340  ->
                       match uu____12340 with
                       | (x,t,uu____12351) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12357 =
                    let uu____12358 =
                      let uu____12359 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12359  in
                    FStar_Parser_AST.mk_term uu____12358
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12357 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12363 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12390  ->
                          match uu____12390 with
                          | (x,uu____12400,uu____12401) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12363)
            | uu____12454 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12485 =
            match uu___100_12485 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12509 = typars_of_binders _env binders  in
                (match uu____12509 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12555 =
                         let uu____12556 =
                           let uu____12557 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12557  in
                         FStar_Parser_AST.mk_term uu____12556
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12555 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id1  in
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
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____12570 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12614 =
              FStar_List.fold_left
                (fun uu____12654  ->
                   fun uu____12655  ->
                     match (uu____12654, uu____12655) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12746 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12746 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12614 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12859 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12859
                | uu____12860 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12868 = desugar_abstract_tc quals env [] tc  in
              (match uu____12868 with
               | (uu____12881,uu____12882,se,uu____12884) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12887,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12904 =
                                 let uu____12905 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12905  in
                               if uu____12904
                               then
                                 let uu____12906 =
                                   let uu____12911 =
                                     let uu____12912 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12912
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12911)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12906
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
                           | uu____12919 ->
                               let uu____12920 =
                                 let uu____12923 =
                                   let uu____12924 =
                                     let uu____12937 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12937)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12924
                                    in
                                 FStar_Syntax_Syntax.mk uu____12923  in
                               uu____12920 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12941 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12941.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12941.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12941.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12944 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____12947 = FStar_ToSyntax_Env.qualify env1 id1
                        in
                     FStar_ToSyntax_Env.push_doc env1 uu____12947
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12962 = typars_of_binders env binders  in
              (match uu____12962 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12998 =
                           FStar_Util.for_some
                             (fun uu___101_13000  ->
                                match uu___101_13000 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____13001 -> false) quals
                            in
                         if uu____12998
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____13008 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_13012  ->
                               match uu___102_13012 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____13013 -> false))
                        in
                     if uu____13008
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id1  in
                   let se =
                     let uu____13022 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____13022
                     then
                       let uu____13025 =
                         let uu____13032 =
                           let uu____13033 = unparen t  in
                           uu____13033.FStar_Parser_AST.tm  in
                         match uu____13032 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____13054 =
                               match FStar_List.rev args with
                               | (last_arg,uu____13084)::args_rev ->
                                   let uu____13096 =
                                     let uu____13097 = unparen last_arg  in
                                     uu____13097.FStar_Parser_AST.tm  in
                                   (match uu____13096 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13125 -> ([], args))
                               | uu____13134 -> ([], args)  in
                             (match uu____13054 with
                              | (cattributes,args1) ->
                                  let uu____13173 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13173))
                         | uu____13184 -> (t, [])  in
                       match uu____13025 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___103_13206  ->
                                     match uu___103_13206 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13207 -> true))
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
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13218)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13242 = tycon_record_as_variant trec  in
              (match uu____13242 with
               | (t,fs) ->
                   let uu____13259 =
                     let uu____13262 =
                       let uu____13263 =
                         let uu____13272 =
                           let uu____13275 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____13275  in
                         (uu____13272, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13263  in
                     uu____13262 :: quals  in
                   desugar_tycon env d uu____13259 [t])
          | uu____13280::uu____13281 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13442 = et  in
                match uu____13442 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13667 ->
                         let trec = tc  in
                         let uu____13691 = tycon_record_as_variant trec  in
                         (match uu____13691 with
                          | (t,fs) ->
                              let uu____13750 =
                                let uu____13753 =
                                  let uu____13754 =
                                    let uu____13763 =
                                      let uu____13766 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13766  in
                                    (uu____13763, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13754
                                   in
                                uu____13753 :: quals1  in
                              collect_tcs uu____13750 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13853 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13853 with
                          | (env2,uu____13913,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____14062 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____14062 with
                          | (env2,uu____14122,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14247 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14294 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14294 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14805  ->
                             match uu___105_14805 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14872,uu____14873);
                                    FStar_Syntax_Syntax.sigrng = uu____14874;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14875;
                                    FStar_Syntax_Syntax.sigmeta = uu____14876;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14877;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14938 =
                                     typars_of_binders env1 binders  in
                                   match uu____14938 with
                                   | (env2,tpars1) ->
                                       let uu____14969 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14969 with
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
                                 let uu____15002 =
                                   let uu____15023 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____15023)
                                    in
                                 [uu____15002]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____15091);
                                    FStar_Syntax_Syntax.sigrng = uu____15092;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15094;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15095;_},constrs,tconstr,quals1)
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
                                 let uu____15191 = push_tparams env1 tpars
                                    in
                                 (match uu____15191 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15268  ->
                                             match uu____15268 with
                                             | (x,uu____15282) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15290 =
                                        let uu____15319 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15433  ->
                                                  match uu____15433 with
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
                                                        let uu____15489 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15489
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___104_15500
                                                                 ->
                                                                match uu___104_15500
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15512
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15520 =
                                                        let uu____15541 =
                                                          let uu____15542 =
                                                            let uu____15543 =
                                                              let uu____15558
                                                                =
                                                                let uu____15561
                                                                  =
                                                                  let uu____15564
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15564
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15561
                                                                 in
                                                              (name, univs1,
                                                                uu____15558,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15543
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15542;
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
                                                          uu____15541)
                                                         in
                                                      (name, uu____15520)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15319
                                         in
                                      (match uu____15290 with
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
                             | uu____15803 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15935  ->
                             match uu____15935 with
                             | (name_doc,uu____15963,uu____15964) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____16044  ->
                             match uu____16044 with
                             | (uu____16065,uu____16066,se) -> se))
                      in
                   let uu____16096 =
                     let uu____16103 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16103 rng
                      in
                   (match uu____16096 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16169  ->
                                  match uu____16169 with
                                  | (uu____16192,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16243,tps,k,uu____16246,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____16265 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16282  ->
                                 match uu____16282 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let desugar_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      let uu____16317 =
        FStar_List.fold_left
          (fun uu____16340  ->
             fun b  ->
               match uu____16340 with
               | (env1,binders1) ->
                   let uu____16360 = desugar_binder env1 b  in
                   (match uu____16360 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16377 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16377 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16394 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16317 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let push_reflect_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_ToSyntax_Env.env
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____16439 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16444  ->
                    match uu___106_16444 with
                    | FStar_Syntax_Syntax.Reflectable uu____16445 -> true
                    | uu____16446 -> false))
             in
          if uu____16439
          then
            let monad_env =
              FStar_ToSyntax_Env.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
                (FStar_ToSyntax_Env.qualify monad_env)
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
            FStar_ToSyntax_Env.push_sigelt env refl_decl
          else env
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                let uu____16545 = desugar_binders monad_env eff_binders  in
                match uu____16545 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16566 =
                        let uu____16567 =
                          let uu____16574 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16574  in
                        FStar_List.length uu____16567  in
                      uu____16566 = (Prims.parse_int "1")  in
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
                          (uu____16616,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16618,uu____16619,uu____16620),uu____16621)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16654 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16655 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16667 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16667 mandatory_members)
                        eff_decls
                       in
                    (match uu____16655 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16684 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16713  ->
                                   fun decl  ->
                                     match uu____16713 with
                                     | (env2,out) ->
                                         let uu____16733 =
                                           desugar_decl env2 decl  in
                                         (match uu____16733 with
                                          | (env3,ses) ->
                                              let uu____16746 =
                                                let uu____16749 =
                                                  FStar_List.hd ses  in
                                                uu____16749 :: out  in
                                              (env3, uu____16746)))
                                (env1, []))
                            in
                         (match uu____16684 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16817,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16820,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16821,
                                                                (def,uu____16823)::
                                                                (cps_type,uu____16825)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16826;
                                                             FStar_Parser_AST.level
                                                               = uu____16827;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16879 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16879 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16899 =
                                                   let uu____16900 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16901 =
                                                     let uu____16902 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16902
                                                      in
                                                   let uu____16907 =
                                                     let uu____16908 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16908
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16900;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16901;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16907
                                                   }  in
                                                 (uu____16899, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16915,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16918,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16953 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16953 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16973 =
                                                   let uu____16974 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____16975 =
                                                     let uu____16976 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16976
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16974;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16975;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16973, doc1))
                                        | uu____16983 ->
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
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____17013 =
                                  let uu____17014 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____17014
                                   in
                                ([], uu____17013)  in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name  in
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
                                    let uu____17031 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____17031)  in
                                  let uu____17038 =
                                    let uu____17039 =
                                      let uu____17040 =
                                        let uu____17041 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____17041
                                         in
                                      let uu____17050 = lookup "return"  in
                                      let uu____17051 = lookup "bind"  in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
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
                                          uu____17040;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____17050;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____17051;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____17039
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____17038;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___107_17055  ->
                                          match uu___107_17055 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____17056 -> true
                                          | uu____17057 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____17067 =
                                     let uu____17068 =
                                       let uu____17069 = lookup "return_wp"
                                          in
                                       let uu____17070 = lookup "bind_wp"  in
                                       let uu____17071 =
                                         lookup "if_then_else"  in
                                       let uu____17072 = lookup "ite_wp"  in
                                       let uu____17073 = lookup "stronger"
                                          in
                                       let uu____17074 = lookup "close_wp"
                                          in
                                       let uu____17075 = lookup "assert_p"
                                          in
                                       let uu____17076 = lookup "assume_p"
                                          in
                                       let uu____17077 = lookup "null_wp"  in
                                       let uu____17078 = lookup "trivial"  in
                                       let uu____17079 =
                                         if rr
                                         then
                                           let uu____17080 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____17080
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____17096 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____17098 =
                                         if rr then lookup "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____17069;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____17070;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____17071;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____17072;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____17073;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____17074;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____17075;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____17076;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____17077;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____17078;
                                         FStar_Syntax_Syntax.repr =
                                           uu____17079;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____17096;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____17098;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____17068
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____17067;
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
                                FStar_ToSyntax_Env.push_sigelt env0 se  in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____17123  ->
                                          match uu____17123 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17137 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____17137
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                push_reflect_effect env5 qualifiers mname
                                  d.FStar_Parser_AST.drange
                                 in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

and desugar_redefine_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                   in
                let uu____17161 = desugar_binders env1 eff_binders  in
                match uu____17161 with
                | (env2,binders) ->
                    let uu____17180 =
                      let uu____17199 = head_and_args defn  in
                      match uu____17199 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17244 ->
                                let uu____17245 =
                                  let uu____17250 =
                                    let uu____17251 =
                                      let uu____17252 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17252 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17251  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17250)
                                   in
                                FStar_Errors.raise_error uu____17245
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17254 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17284)::args_rev ->
                                let uu____17296 =
                                  let uu____17297 = unparen last_arg  in
                                  uu____17297.FStar_Parser_AST.tm  in
                                (match uu____17296 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17325 -> ([], args))
                            | uu____17334 -> ([], args)  in
                          (match uu____17254 with
                           | (cattributes,args1) ->
                               let uu____17385 = desugar_args env2 args1  in
                               let uu____17394 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17385, uu____17394))
                       in
                    (match uu____17180 with
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
                          (let uu____17450 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17450 with
                           | (ed_binders,uu____17464,ed_binders_opening) ->
                               let sub1 uu____17475 =
                                 match uu____17475 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17489 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17489 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17493 =
                                       let uu____17494 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17494)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17493
                                  in
                               let mname =
                                 FStar_ToSyntax_Env.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17499 =
                                   let uu____17500 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17500
                                    in
                                 let uu____17511 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17512 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17513 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17514 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17515 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17516 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17517 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17518 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17519 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17520 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17521 =
                                   let uu____17522 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17522
                                    in
                                 let uu____17533 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17534 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17535 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17543 =
                                          FStar_ToSyntax_Env.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17544 =
                                          let uu____17545 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17545
                                           in
                                        let uu____17556 =
                                          let uu____17557 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17557
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17543;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17544;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17556
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
                                     uu____17499;
                                   FStar_Syntax_Syntax.ret_wp = uu____17511;
                                   FStar_Syntax_Syntax.bind_wp = uu____17512;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17513;
                                   FStar_Syntax_Syntax.ite_wp = uu____17514;
                                   FStar_Syntax_Syntax.stronger = uu____17515;
                                   FStar_Syntax_Syntax.close_wp = uu____17516;
                                   FStar_Syntax_Syntax.assert_p = uu____17517;
                                   FStar_Syntax_Syntax.assume_p = uu____17518;
                                   FStar_Syntax_Syntax.null_wp = uu____17519;
                                   FStar_Syntax_Syntax.trivial = uu____17520;
                                   FStar_Syntax_Syntax.repr = uu____17521;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17533;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17534;
                                   FStar_Syntax_Syntax.actions = uu____17535
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17570 =
                                     let uu____17571 =
                                       let uu____17578 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17578
                                        in
                                     FStar_List.length uu____17571  in
                                   uu____17570 = (Prims.parse_int "1")  in
                                 let uu____17607 =
                                   let uu____17610 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17610 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17607;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_ToSyntax_Env.push_sigelt env0 se  in
                               let env4 =
                                 FStar_ToSyntax_Env.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_ToSyntax_Env.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____17630 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_ToSyntax_Env.push_sigelt
                                               env5 uu____17630
                                              in
                                           FStar_ToSyntax_Env.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17632 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17632
                                 then
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
                                       (FStar_ToSyntax_Env.qualify monad_env)
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
                                   FStar_ToSyntax_Env.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_ToSyntax_Env.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun d  ->
    let uu____17647 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17647 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17698 ->
              let uu____17699 =
                let uu____17700 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17700
                 in
              Prims.strcat "\n  " uu____17699
          | uu____17701 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17714  ->
               match uu____17714 with
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
          let uu____17732 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17732
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17734 =
          let uu____17743 = FStar_Syntax_Syntax.as_arg arg  in [uu____17743]
           in
        FStar_Syntax_Util.mk_app fv uu____17734

and desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17750 = desugar_decl_noattrs env d  in
      match uu____17750 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17770 = mk_comment_attr d  in uu____17770 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17781 =
                     let uu____17782 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17782  in
                   Prims.strcat s uu____17781) "" attrs2
             in
          let uu____17783 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17789 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17789.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17789.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17789.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17789.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17783)

and desugar_decl_noattrs :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17815 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17831 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____17831, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17870  ->
                 match uu____17870 with | (x,uu____17878) -> x) tcs
             in
          let uu____17883 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17883 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17905;
                    FStar_Parser_AST.prange = uu____17906;_},uu____17907)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17916;
                    FStar_Parser_AST.prange = uu____17917;_},uu____17918)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17933;
                         FStar_Parser_AST.prange = uu____17934;_},uu____17935);
                    FStar_Parser_AST.prange = uu____17936;_},uu____17937)::[]
                   -> false
               | (p,uu____17953)::[] ->
                   let uu____17962 = is_app_pattern p  in
                   Prims.op_Negation uu____17962
               | uu____17963 -> false)
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
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____18037 =
              let uu____18038 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____18038.FStar_Syntax_Syntax.n  in
            (match uu____18037 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____18046) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____18079::uu____18080 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____18083 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18097  ->
                               match uu___108_18097 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18100;
                                   FStar_Syntax_Syntax.lbunivs = uu____18101;
                                   FStar_Syntax_Syntax.lbtyp = uu____18102;
                                   FStar_Syntax_Syntax.lbeff = uu____18103;
                                   FStar_Syntax_Syntax.lbdef = uu____18104;
                                   FStar_Syntax_Syntax.lbattrs = uu____18105;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18117;
                                   FStar_Syntax_Syntax.lbtyp = uu____18118;
                                   FStar_Syntax_Syntax.lbeff = uu____18119;
                                   FStar_Syntax_Syntax.lbdef = uu____18120;
                                   FStar_Syntax_Syntax.lbattrs = uu____18121;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18135 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18166  ->
                             match uu____18166 with
                             | (uu____18179,(uu____18180,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18135
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18204 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18204
                   then
                     let uu____18213 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18227 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18229 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18229.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18229.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18227.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18227.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18227.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18227.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18227.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18213)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let attrs =
                   FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = attrs
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id1  ->
                          FStar_ToSyntax_Env.push_doc env2 id1
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____18264 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18270 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18289 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18270 with
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
                       let uu___136_18313 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18313.FStar_Parser_AST.prange)
                       }
                   | uu____18314 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18321 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18321.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18321.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18321.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18353 id1 =
                   match uu____18353 with
                   | (env1,ses) ->
                       let main =
                         let uu____18374 =
                           let uu____18375 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18375  in
                         FStar_Parser_AST.mk_term uu____18374
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
                       let uu____18425 = desugar_decl env1 id_decl  in
                       (match uu____18425 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18443 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18443 FStar_Util.set_elements
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
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc  in
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
            let uu____18474 = close_fun env t  in
            desugar_term env uu____18474  in
          let quals1 =
            let uu____18478 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____18478
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id1  in
          let se =
            let uu____18484 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18484;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18496 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18496 with
           | (t,uu____18510) ->
               let l = FStar_ToSyntax_Env.qualify env id1  in
               let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
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
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____18544 =
              let uu____18551 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18551]  in
            let uu____18552 =
              let uu____18555 =
                let uu____18556 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18556  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18555
               in
            FStar_Syntax_Util.arrow uu____18544 uu____18552  in
          let l = FStar_ToSyntax_Env.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
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
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
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
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____18618 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____18618 with
            | FStar_Pervasives_Native.None  ->
                let uu____18621 =
                  let uu____18626 =
                    let uu____18627 =
                      let uu____18628 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18628 " not found"  in
                    Prims.strcat "Effect name " uu____18627  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18626)  in
                FStar_Errors.raise_error uu____18621
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____18632 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18674 =
                  let uu____18683 =
                    let uu____18690 = desugar_term env t  in
                    ([], uu____18690)  in
                  FStar_Pervasives_Native.Some uu____18683  in
                (uu____18674, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18723 =
                  let uu____18732 =
                    let uu____18739 = desugar_term env wp  in
                    ([], uu____18739)  in
                  FStar_Pervasives_Native.Some uu____18732  in
                let uu____18748 =
                  let uu____18757 =
                    let uu____18764 = desugar_term env t  in
                    ([], uu____18764)  in
                  FStar_Pervasives_Native.Some uu____18757  in
                (uu____18723, uu____18748)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18790 =
                  let uu____18799 =
                    let uu____18806 = desugar_term env t  in
                    ([], uu____18806)  in
                  FStar_Pervasives_Native.Some uu____18799  in
                (FStar_Pervasives_Native.None, uu____18790)
             in
          (match uu____18632 with
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

let desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun decls  ->
      let uu____18894 =
        FStar_List.fold_left
          (fun uu____18914  ->
             fun d  ->
               match uu____18914 with
               | (env1,sigelts) ->
                   let uu____18934 = desugar_decl env1 d  in
                   (match uu____18934 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18894 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18975 =
            match uu___110_18975 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18989,FStar_Syntax_Syntax.Sig_let uu____18990) ->
                     let uu____19003 =
                       let uu____19006 =
                         let uu___138_19007 = se2  in
                         let uu____19008 =
                           let uu____19011 =
                             FStar_List.filter
                               (fun uu___109_19025  ->
                                  match uu___109_19025 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____19029;
                                           FStar_Syntax_Syntax.vars =
                                             uu____19030;_},uu____19031);
                                      FStar_Syntax_Syntax.pos = uu____19032;
                                      FStar_Syntax_Syntax.vars = uu____19033;_}
                                      when
                                      let uu____19056 =
                                        let uu____19057 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____19057
                                         in
                                      uu____19056 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____19058 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____19011
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_19007.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_19007.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_19007.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_19007.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____19008
                         }  in
                       uu____19006 :: se1 :: acc  in
                     forward uu____19003 sigelts1
                 | uu____19063 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____19071 = forward [] sigelts  in (env1, uu____19071)
  
let open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____19122) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19126;
               FStar_Syntax_Syntax.exports = uu____19127;
               FStar_Syntax_Syntax.is_interface = uu____19128;_},FStar_Parser_AST.Module
             (current_lid,uu____19130)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19138) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____19141 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19177 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19177, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19194 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii
                 in
              (uu____19194, mname, decls, false)
           in
        match uu____19141 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19224 = desugar_decls env2 decls  in
            (match uu____19224 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____19278 =
            (FStar_Options.interactive ()) &&
              (let uu____19280 =
                 let uu____19281 =
                   let uu____19282 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19282  in
                 FStar_Util.get_file_extension uu____19281  in
               FStar_List.mem uu____19280 ["fsti"; "fsi"])
             in
          if uu____19278 then as_interface m else m  in
        let uu____19286 = desugar_modul_common curmod env m1  in
        match uu____19286 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19301 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____19317 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19317 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____19333 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____19333
            then
              let uu____19334 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____19334
            else ());
           (let uu____19336 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____19336, modul)))
  
let ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____19350 = desugar_modul env modul  in
      match uu____19350 with | (env1,modul1) -> (modul1, env1)
  
let decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____19377 = desugar_decls env decls  in
      match uu____19377 with | (env1,sigelts) -> (sigelts, env1)
  
let partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19415 = desugar_partial_modul modul env a_modul  in
        match uu____19415 with | (env1,modul1) -> (modul1, env1)
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____19489 ->
                  let t =
                    let uu____19497 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19497  in
                  let uu____19506 =
                    let uu____19507 = FStar_Syntax_Subst.compress t  in
                    uu____19507.FStar_Syntax_Syntax.n  in
                  (match uu____19506 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19517,uu____19518)
                       -> bs1
                   | uu____19539 -> failwith "Impossible")
               in
            let uu____19546 =
              let uu____19553 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19553
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19546 with
            | (binders,uu____19555,binders_opening) ->
                let erase_term t =
                  let uu____19561 =
                    let uu____19562 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19562  in
                  FStar_Syntax_Subst.close binders uu____19561  in
                let erase_tscheme uu____19578 =
                  match uu____19578 with
                  | (us,t) ->
                      let t1 =
                        let uu____19598 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19598 t  in
                      let uu____19601 =
                        let uu____19602 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19602  in
                      ([], uu____19601)
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
                    | uu____19631 ->
                        let bs =
                          let uu____19639 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19639  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19669 =
                          let uu____19670 =
                            let uu____19673 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19673  in
                          uu____19670.FStar_Syntax_Syntax.n  in
                        (match uu____19669 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19681,uu____19682) -> bs1
                         | uu____19703 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19714 =
                      let uu____19715 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19715  in
                    FStar_Syntax_Subst.close binders uu____19714  in
                  let uu___139_19716 = action  in
                  let uu____19717 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19718 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19716.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19716.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19717;
                    FStar_Syntax_Syntax.action_typ = uu____19718
                  }  in
                let uu___140_19719 = ed  in
                let uu____19720 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19721 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19722 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19723 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19724 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19725 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19726 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19727 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19728 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19729 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19730 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19731 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19732 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19733 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19734 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19735 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19719.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19719.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19720;
                  FStar_Syntax_Syntax.signature = uu____19721;
                  FStar_Syntax_Syntax.ret_wp = uu____19722;
                  FStar_Syntax_Syntax.bind_wp = uu____19723;
                  FStar_Syntax_Syntax.if_then_else = uu____19724;
                  FStar_Syntax_Syntax.ite_wp = uu____19725;
                  FStar_Syntax_Syntax.stronger = uu____19726;
                  FStar_Syntax_Syntax.close_wp = uu____19727;
                  FStar_Syntax_Syntax.assert_p = uu____19728;
                  FStar_Syntax_Syntax.assume_p = uu____19729;
                  FStar_Syntax_Syntax.null_wp = uu____19730;
                  FStar_Syntax_Syntax.trivial = uu____19731;
                  FStar_Syntax_Syntax.repr = uu____19732;
                  FStar_Syntax_Syntax.return_repr = uu____19733;
                  FStar_Syntax_Syntax.bind_repr = uu____19734;
                  FStar_Syntax_Syntax.actions = uu____19735
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19747 = se  in
                  let uu____19748 =
                    let uu____19749 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19749  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19748;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19747.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19747.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19747.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19747.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19753 = se  in
                  let uu____19754 =
                    let uu____19755 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19755
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19754;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19753.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19753.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19753.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19753.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19757 -> FStar_ToSyntax_Env.push_sigelt env se  in
          let uu____19758 =
            FStar_ToSyntax_Env.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19758 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19770 =
                  FStar_ToSyntax_Env.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19770
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_ToSyntax_Env.finish en2 m  in
              let uu____19772 =
                if pop_when_done
                then
                  FStar_ToSyntax_Env.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19772)
  