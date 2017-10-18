open Prims
let desugar_disjunctive_pattern:
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
let trans_aqual:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___217_62  ->
    match uu___217_62 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____67 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___218_83  ->
        match uu___218_83 with
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
            (FStar_Errors.warn r
               "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).";
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline  ->
            FStar_Exn.raise (FStar_Errors.Error ("Unsupported qualifier", r))
        | FStar_Parser_AST.Visible  ->
            FStar_Exn.raise (FStar_Errors.Error ("Unsupported qualifier", r))
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___219_91  ->
    match uu___219_91 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___220_101  ->
    match uu___220_101 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____104 -> FStar_Pervasives_Native.None
let arg_withimp_e:
  'Auu____111 .
    FStar_Parser_AST.imp ->
      'Auu____111 ->
        ('Auu____111,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp))
let arg_withimp_t:
  'Auu____134 .
    FStar_Parser_AST.imp ->
      'Auu____134 ->
        ('Auu____134,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____151 -> (t, FStar_Pervasives_Native.None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____167 -> true
            | uu____172 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____178 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____183 =
      let uu____184 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____184 in
    FStar_Parser_AST.mk_term uu____183 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____189 =
      let uu____190 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____190 in
    FStar_Parser_AST.mk_term uu____189 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____200 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____206) ->
          let uu____219 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____219 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____225,uu____226) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____229,uu____230) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____235,t1) -> is_comp_type env t1
      | uu____237 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____250 =
          let uu____253 =
            let uu____254 =
              let uu____259 = FStar_Parser_AST.compile_op n1 s r in
              (uu____259, r) in
            FStar_Ident.mk_ident uu____254 in
          [uu____253] in
        FStar_All.pipe_right uu____250 FStar_Ident.lid_of_ids
let op_as_term:
  'Auu____272 .
    FStar_ToSyntax_Env.env ->
      Prims.int ->
        'Auu____272 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____300 =
              let uu____301 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None in
              FStar_All.pipe_right uu____301 FStar_Syntax_Syntax.fv_to_tm in
            FStar_Pervasives_Native.Some uu____300 in
          let fallback uu____307 =
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
                let uu____310 = FStar_Options.ml_ish () in
                if uu____310
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
            | uu____314 -> FStar_Pervasives_Native.None in
          let uu____315 =
            let uu____322 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange in
            FStar_ToSyntax_Env.try_lookup_lid env uu____322 in
          match uu____315 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____334 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____351 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____351
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____390 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____394 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____394 with | (env1,uu____406) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____409,term) ->
          let uu____411 = free_type_vars env term in (env, uu____411)
      | FStar_Parser_AST.TAnnotated (id,uu____417) ->
          let uu____418 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____418 with | (env1,uu____430) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____434 = free_type_vars env t in (env, uu____434)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____441 =
        let uu____442 = unparen t in uu____442.FStar_Parser_AST.tm in
      match uu____441 with
      | FStar_Parser_AST.Labeled uu____445 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____455 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____455 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____468 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____475 -> []
      | FStar_Parser_AST.Uvar uu____476 -> []
      | FStar_Parser_AST.Var uu____477 -> []
      | FStar_Parser_AST.Projector uu____478 -> []
      | FStar_Parser_AST.Discrim uu____483 -> []
      | FStar_Parser_AST.Name uu____484 -> []
      | FStar_Parser_AST.Assign (uu____485,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____488) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____494) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____499,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____515,ts) ->
          FStar_List.collect
            (fun uu____536  ->
               match uu____536 with | (t1,uu____544) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____545,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____553) ->
          let uu____554 = free_type_vars env t1 in
          let uu____557 = free_type_vars env t2 in
          FStar_List.append uu____554 uu____557
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____562 = free_type_vars_b env b in
          (match uu____562 with
           | (env1,f) ->
               let uu____577 = free_type_vars env1 t1 in
               FStar_List.append f uu____577)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____586 =
            FStar_List.fold_left
              (fun uu____606  ->
                 fun binder  ->
                   match uu____606 with
                   | (env1,free) ->
                       let uu____626 = free_type_vars_b env1 binder in
                       (match uu____626 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____586 with
           | (env1,free) ->
               let uu____657 = free_type_vars env1 body in
               FStar_List.append free uu____657)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____666 =
            FStar_List.fold_left
              (fun uu____686  ->
                 fun binder  ->
                   match uu____686 with
                   | (env1,free) ->
                       let uu____706 = free_type_vars_b env1 binder in
                       (match uu____706 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____666 with
           | (env1,free) ->
               let uu____737 = free_type_vars env1 body in
               FStar_List.append free uu____737)
      | FStar_Parser_AST.Project (t1,uu____741) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____745 -> []
      | FStar_Parser_AST.Let uu____752 -> []
      | FStar_Parser_AST.LetOpen uu____765 -> []
      | FStar_Parser_AST.If uu____770 -> []
      | FStar_Parser_AST.QForall uu____777 -> []
      | FStar_Parser_AST.QExists uu____790 -> []
      | FStar_Parser_AST.Record uu____803 -> []
      | FStar_Parser_AST.Match uu____816 -> []
      | FStar_Parser_AST.TryWith uu____831 -> []
      | FStar_Parser_AST.Bind uu____846 -> []
      | FStar_Parser_AST.Seq uu____853 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____901 =
        let uu____902 = unparen t1 in uu____902.FStar_Parser_AST.tm in
      match uu____901 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____944 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____966 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____966 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____984 =
                     let uu____985 =
                       let uu____990 = tm_type x.FStar_Ident.idRange in
                       (x, uu____990) in
                     FStar_Parser_AST.TAnnotated uu____985 in
                   FStar_Parser_AST.mk_binder uu____984 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
         result)
let close_fun:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1005 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1005 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1023 =
                     let uu____1024 =
                       let uu____1029 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1029) in
                     FStar_Parser_AST.TAnnotated uu____1024 in
                   FStar_Parser_AST.mk_binder uu____1023
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1031 =
             let uu____1032 = unparen t in uu____1032.FStar_Parser_AST.tm in
           match uu____1031 with
           | FStar_Parser_AST.Product uu____1033 -> t
           | uu____1040 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level in
         result)
let rec uncurry:
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
      | uu____1074 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1081,uu____1082) -> true
    | FStar_Parser_AST.PatVar (uu____1087,uu____1088) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1094) -> is_var_pattern p1
    | uu____1095 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1101) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1102;
           FStar_Parser_AST.prange = uu____1103;_},uu____1104)
        -> true
    | uu____1115 -> false
let replace_unit_pattern:
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1120 -> p
let rec destruct_app_pattern:
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
            let uu____1163 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1163 with
             | (name,args,uu____1194) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1220);
               FStar_Parser_AST.prange = uu____1221;_},args)
            when is_top_level1 ->
            let uu____1231 =
              let uu____1236 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____1236 in
            (uu____1231, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1246);
               FStar_Parser_AST.prange = uu____1247;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1265 -> failwith "Not an app pattern"
let rec gather_pattern_bound_vars_maybe_top:
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1305 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1306,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1309 -> acc
      | FStar_Parser_AST.PatTvar uu____1310 -> acc
      | FStar_Parser_AST.PatOp uu____1317 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1325) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1334) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1349 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1349
      | FStar_Parser_AST.PatAscribed (pat,uu____1357) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1397 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1427 -> false
let __proj__LetBinder__item___0:
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___221_1455  ->
    match uu___221_1455 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1462 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun imp  ->
      fun uu___222_1490  ->
        match uu___222_1490 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1506 = FStar_Syntax_Syntax.null_binder k in
            (uu____1506, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1511 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1511 with
             | (env1,a1) ->
                 (((let uu___245_1531 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___245_1531.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___245_1531.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1551  ->
    match uu____1551 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
let mk_ref_read:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1604 =
        let uu____1619 =
          let uu____1620 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1620 in
        let uu____1621 =
          let uu____1630 =
            let uu____1637 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1637) in
          [uu____1630] in
        (uu____1619, uu____1621) in
      FStar_Syntax_Syntax.Tm_app uu____1604 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1671 =
        let uu____1686 =
          let uu____1687 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1687 in
        let uu____1688 =
          let uu____1697 =
            let uu____1704 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1704) in
          [uu____1697] in
        (uu____1686, uu____1688) in
      FStar_Syntax_Syntax.Tm_app uu____1671 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let mk_ref_assign:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1750 =
            let uu____1765 =
              let uu____1766 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____1766 in
            let uu____1767 =
              let uu____1776 =
                let uu____1783 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____1783) in
              let uu____1786 =
                let uu____1795 =
                  let uu____1802 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____1802) in
                [uu____1795] in
              uu____1776 :: uu____1786 in
            (uu____1765, uu____1767) in
          FStar_Syntax_Syntax.Tm_app uu____1750 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___223_1834  ->
    match uu___223_1834 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1835 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1845 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1845)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1862 =
      let uu____1863 = unparen t in uu____1863.FStar_Parser_AST.tm in
    match uu____1862 with
    | FStar_Parser_AST.Wild  ->
        let uu____1868 =
          let uu____1869 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1869 in
        FStar_Util.Inr uu____1868
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1880)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Exn.raise
             (FStar_Errors.Error
                ((Prims.strcat
                    "Negative universe constant  are not supported : " repr),
                  (t.FStar_Parser_AST.range)))
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____1946 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1946
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1957 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1957
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1968 =
               let uu____1969 =
                 let uu____1974 =
                   let uu____1975 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1975 in
                 (uu____1974, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1969 in
             FStar_Exn.raise uu____1968)
    | FStar_Parser_AST.App uu____1980 ->
        let rec aux t1 univargs =
          let uu____2010 =
            let uu____2011 = unparen t1 in uu____2011.FStar_Parser_AST.tm in
          match uu____2010 with
          | FStar_Parser_AST.App (t2,targ,uu____2018) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___224_2042  ->
                     match uu___224_2042 with
                     | FStar_Util.Inr uu____2047 -> true
                     | uu____2048 -> false) univargs
              then
                let uu____2053 =
                  let uu____2054 =
                    FStar_List.map
                      (fun uu___225_2063  ->
                         match uu___225_2063 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2054 in
                FStar_Util.Inr uu____2053
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___226_2080  ->
                        match uu___226_2080 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2086 -> failwith "impossible")
                     univargs in
                 let uu____2087 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2087)
          | uu____2093 ->
              let uu____2094 =
                let uu____2095 =
                  let uu____2100 =
                    let uu____2101 =
                      let uu____2102 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____2102 " in universe context" in
                    Prims.strcat "Unexpected term " uu____2101 in
                  (uu____2100, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____2095 in
              FStar_Exn.raise uu____2094 in
        aux t []
    | uu____2111 ->
        let uu____2112 =
          let uu____2113 =
            let uu____2118 =
              let uu____2119 =
                let uu____2120 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____2120 " in universe context" in
              Prims.strcat "Unexpected term " uu____2119 in
            (uu____2118, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____2113 in
        FStar_Exn.raise uu____2112
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields:
  'Auu____2144 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2144) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2169 = FStar_List.hd fields in
        match uu____2169 with
        | (f,uu____2179) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
              let check_field uu____2189 =
                match uu____2189 with
                | (f',uu____2195) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2197 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record in
                      if uu____2197
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                             f'.FStar_Ident.str in
                         FStar_Exn.raise (FStar_Errors.Error (msg, rg))))) in
              (let uu____2201 = FStar_List.tl fields in
               FStar_List.iter check_field uu____2201);
              (match () with | () -> record)))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2415 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2422 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2423 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2425,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2465  ->
                          match uu____2465 with
                          | (p3,uu____2475) ->
                              let uu____2476 = pat_vars p3 in
                              FStar_Util.set_union out uu____2476)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2480) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2481) -> ()
         | (true ,uu____2488) ->
             FStar_Exn.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____2523 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2523 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2537 ->
               let uu____2540 = push_bv_maybe_mut e x in
               (match uu____2540 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           let orig = p1 in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2627 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2643 =
                 let uu____2644 =
                   let uu____2645 =
                     let uu____2652 =
                       let uu____2653 =
                         let uu____2658 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2658, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2653 in
                     (uu____2652, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2645 in
                 {
                   FStar_Parser_AST.pat = uu____2644;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2643
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2663 = aux loc env1 p2 in
               (match uu____2663 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___246_2717 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___247_2722 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___247_2722.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___247_2722.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___246_2717.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___248_2724 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___249_2729 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___249_2729.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___249_2729.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___248_2724.FStar_Syntax_Syntax.p)
                          }
                      | uu____2730 when top -> p4
                      | uu____2731 ->
                          FStar_Exn.raise
                            (FStar_Errors.Error
                               ("Type ascriptions within patterns are only allowed on variables",
                                 (orig.FStar_Parser_AST.prange))) in
                    let uu____2734 =
                      match binder with
                      | LetBinder uu____2747 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2761 = close_fun env1 t in
                            desugar_term env1 uu____2761 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2763 -> true)
                           then
                             (let uu____2764 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2765 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2766 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                uu____2764 uu____2765 uu____2766)
                           else ();
                           (let uu____2768 = annot_pat_var p3 t1 in
                            (uu____2768,
                              (LocalBinder
                                 ((let uu___250_2774 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___250_2774.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___250_2774.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq))))) in
                    (match uu____2734 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2796 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2796, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2807 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2807, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2828 = resolvex loc env1 x in
               (match uu____2828 with
                | (loc1,env2,xbv) ->
                    let uu____2850 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2850, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2871 = resolvex loc env1 x in
               (match uu____2871 with
                | (loc1,env2,xbv) ->
                    let uu____2893 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2893, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2905 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2905, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2929;_},args)
               ->
               let uu____2935 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2976  ->
                        match uu____2976 with
                        | (loc1,env2,args1) ->
                            let uu____3024 = aux loc1 env2 arg in
                            (match uu____3024 with
                             | (loc2,env3,uu____3053,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2935 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3123 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3123, false))
           | FStar_Parser_AST.PatApp uu____3140 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3162 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3195  ->
                        match uu____3195 with
                        | (loc1,env2,pats1) ->
                            let uu____3227 = aux loc1 env2 pat in
                            (match uu____3227 with
                             | (loc2,env3,uu____3252,pat1,uu____3254) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3162 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3297 =
                        let uu____3300 =
                          let uu____3305 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3305 in
                        let uu____3306 =
                          let uu____3307 =
                            let uu____3320 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3320, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3307 in
                        FStar_All.pipe_left uu____3300 uu____3306 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3352 =
                               let uu____3353 =
                                 let uu____3366 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3366, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3353 in
                             FStar_All.pipe_left (pos_r r) uu____3352) pats1
                        uu____3297 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3410 =
                 FStar_List.fold_left
                   (fun uu____3450  ->
                      fun p2  ->
                        match uu____3450 with
                        | (loc1,env2,pats) ->
                            let uu____3499 = aux loc1 env2 p2 in
                            (match uu____3499 with
                             | (loc2,env3,uu____3528,pat,uu____3530) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3410 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1 in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange in
                    let uu____3625 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3625 with
                     | (constr,uu____3647) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3650 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3652 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3652, false)))
           | FStar_Parser_AST.PatRecord [] ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____3723  ->
                         match uu____3723 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3753  ->
                         match uu____3753 with
                         | (f,uu____3759) ->
                             let uu____3760 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3786  ->
                                       match uu____3786 with
                                       | (g,uu____3792) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3760 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3797,p2)
                                  -> p2))) in
               let app =
                 let uu____3804 =
                   let uu____3805 =
                     let uu____3812 =
                       let uu____3813 =
                         let uu____3814 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3814 in
                       FStar_Parser_AST.mk_pattern uu____3813
                         p1.FStar_Parser_AST.prange in
                     (uu____3812, args) in
                   FStar_Parser_AST.PatApp uu____3805 in
                 FStar_Parser_AST.mk_pattern uu____3804
                   p1.FStar_Parser_AST.prange in
               let uu____3817 = aux loc env1 app in
               (match uu____3817 with
                | (env2,e,b,p2,uu____3846) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3874 =
                            let uu____3875 =
                              let uu____3888 =
                                let uu___251_3889 = fv in
                                let uu____3890 =
                                  let uu____3893 =
                                    let uu____3894 =
                                      let uu____3901 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3901) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3894 in
                                  FStar_Pervasives_Native.Some uu____3893 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___251_3889.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___251_3889.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3890
                                } in
                              (uu____3888, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3875 in
                          FStar_All.pipe_left pos uu____3874
                      | uu____3928 -> p2 in
                    (env2, e, b, p3, false))
         and aux loc env1 p1 = aux' false loc env1 p1 in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3978 = aux' true loc env1 p2 in
               (match uu____3978 with
                | (loc1,env2,var,p3,uu____4005) ->
                    let uu____4010 =
                      FStar_List.fold_left
                        (fun uu____4042  ->
                           fun p4  ->
                             match uu____4042 with
                             | (loc2,env3,ps1) ->
                                 let uu____4075 = aux' true loc2 env3 p4 in
                                 (match uu____4075 with
                                  | (loc3,env4,uu____4100,p5,uu____4102) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4010 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4153 ->
               let uu____4154 = aux' true loc env1 p1 in
               (match uu____4154 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4194 = aux_maybe_or env p in
         match uu____4194 with
         | (env1,b,pats) ->
             ((let uu____4225 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4225);
              (env1, b, pats)))
and desugar_binding_pat_maybe_top:
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
            let uu____4260 =
              let uu____4261 =
                let uu____4266 = FStar_ToSyntax_Env.qualify env x in
                (uu____4266, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4261 in
            (env, uu____4260, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4286 =
                  let uu____4287 =
                    let uu____4292 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4292, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4287 in
                mklet uu____4286
            | FStar_Parser_AST.PatVar (x,uu____4294) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4300);
                   FStar_Parser_AST.prange = uu____4301;_},t)
                ->
                let uu____4307 =
                  let uu____4308 =
                    let uu____4313 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4314 = desugar_term env t in
                    (uu____4313, uu____4314) in
                  LetBinder uu____4308 in
                (env, uu____4307, [])
            | uu____4317 ->
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4327 = desugar_data_pat env p is_mut in
             match uu____4327 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4356;
                       FStar_Syntax_Syntax.p = uu____4357;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4362;
                       FStar_Syntax_Syntax.p = uu____4363;_}::[] -> []
                   | uu____4368 -> p1 in
                 (env1, binder, p2))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun uu____4375  ->
    fun env  ->
      fun pat  ->
        let uu____4378 = desugar_data_pat env pat false in
        match uu____4378 with | (env1,uu____4394,pat1) -> (env1, pat1)
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p
and desugar_term:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false in
      desugar_term_maybe_top false env1 e
and desugar_typ:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true in
      desugar_term_maybe_top false env1 e
and desugar_machine_integer:
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun repr  ->
      fun uu____4412  ->
        fun range  ->
          match uu____4412 with
          | (signedness,width) ->
              let uu____4420 = FStar_Const.bounds signedness width in
              (match uu____4420 with
               | (lower,upper) ->
                   let value =
                     let uu____4428 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4428 in
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
                              | FStar_Const.Int64  -> "64"))) in
                   (if
                      Prims.op_Negation
                        ((lower <= value) && (value <= upper))
                    then
                      (let uu____4431 =
                         let uu____4432 =
                           let uu____4437 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____4437, range) in
                         FStar_Errors.Error uu____4432 in
                       FStar_Exn.raise uu____4431)
                    else ();
                    (let private_intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat ".__"
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t")) in
                     let intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat "."
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t")) in
                     let lid =
                       FStar_Ident.lid_of_path
                         (FStar_Ident.path_of_text intro_nm) range in
                     let lid1 =
                       let uu____4445 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4445 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4455)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____4465 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____4465 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___252_4466 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___252_4466.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___252_4466.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4467 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4474 =
                             let uu____4475 =
                               let uu____4480 =
                                 FStar_Util.format1
                                   "Unexpected numeric literal.  Restart F* to load %s."
                                   tnm in
                               (uu____4480, range) in
                             FStar_Errors.Error uu____4475 in
                           FStar_Exn.raise uu____4474 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____4496 =
                       let uu____4499 =
                         let uu____4500 =
                           let uu____4515 =
                             let uu____4524 =
                               let uu____4531 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4531) in
                             [uu____4524] in
                           (lid1, uu____4515) in
                         FStar_Syntax_Syntax.Tm_app uu____4500 in
                       FStar_Syntax_Syntax.mk uu____4499 in
                     uu____4496 FStar_Pervasives_Native.None range)))
and desugar_name:
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
            let uu____4570 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4570 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4585 =
                    let uu____4586 =
                      let uu____4593 = mk_ref_read tm1 in
                      (uu____4593,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4586 in
                  FStar_All.pipe_left mk1 uu____4585
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4609 =
          let uu____4610 = unparen t in uu____4610.FStar_Parser_AST.tm in
        match uu____4609 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4611; FStar_Ident.ident = uu____4612;
              FStar_Ident.nsstr = uu____4613; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4616 ->
            let uu____4617 =
              let uu____4618 =
                let uu____4623 =
                  let uu____4624 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4624 in
                (uu____4623, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4618 in
            FStar_Exn.raise uu____4617 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range in
        let setpos e =
          let uu___253_4644 = e in
          {
            FStar_Syntax_Syntax.n = (uu___253_4644.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___253_4644.FStar_Syntax_Syntax.vars)
          } in
        let uu____4647 =
          let uu____4648 = unparen top in uu____4648.FStar_Parser_AST.tm in
        match uu____4647 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4649 -> desugar_formula env top
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
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4700::uu____4701::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4705 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4705 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4718;_},t1::t2::[])
                  ->
                  let uu____4723 = flatten1 t1 in
                  FStar_List.append uu____4723 [t2]
              | uu____4726 -> [t] in
            let targs =
              let uu____4730 =
                let uu____4733 = unparen top in flatten1 uu____4733 in
              FStar_All.pipe_right uu____4730
                (FStar_List.map
                   (fun t  ->
                      let uu____4741 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4741)) in
            let uu____4742 =
              let uu____4747 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4747 in
            (match uu____4742 with
             | (tup,uu____4753) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4757 =
              let uu____4760 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4760 in
            FStar_All.pipe_left setpos uu____4757
        | FStar_Parser_AST.Uvar u ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4780 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____4780 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: "
                          (FStar_Ident.text_of_id s)),
                        (top.FStar_Parser_AST.range)))
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4812 = desugar_term env t in
                             (uu____4812, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4826)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4841 =
              let uu___254_4842 = top in
              let uu____4843 =
                let uu____4844 =
                  let uu____4851 =
                    let uu___255_4852 = top in
                    let uu____4853 =
                      let uu____4854 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4854 in
                    {
                      FStar_Parser_AST.tm = uu____4853;
                      FStar_Parser_AST.range =
                        (uu___255_4852.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___255_4852.FStar_Parser_AST.level)
                    } in
                  (uu____4851, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4844 in
              {
                FStar_Parser_AST.tm = uu____4843;
                FStar_Parser_AST.range =
                  (uu___254_4842.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___254_4842.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4841
        | FStar_Parser_AST.Construct (n1,(a,uu____4857)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____4872 =
              let uu___256_4873 = top in
              let uu____4874 =
                let uu____4875 =
                  let uu____4882 =
                    let uu___257_4883 = top in
                    let uu____4884 =
                      let uu____4885 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4885 in
                    {
                      FStar_Parser_AST.tm = uu____4884;
                      FStar_Parser_AST.range =
                        (uu___257_4883.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___257_4883.FStar_Parser_AST.level)
                    } in
                  (uu____4882, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4875 in
              {
                FStar_Parser_AST.tm = uu____4874;
                FStar_Parser_AST.range =
                  (uu___256_4873.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___256_4873.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4872
        | FStar_Parser_AST.Construct (n1,(a,uu____4888)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4903 =
              let uu___258_4904 = top in
              let uu____4905 =
                let uu____4906 =
                  let uu____4913 =
                    let uu___259_4914 = top in
                    let uu____4915 =
                      let uu____4916 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4916 in
                    {
                      FStar_Parser_AST.tm = uu____4915;
                      FStar_Parser_AST.range =
                        (uu___259_4914.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___259_4914.FStar_Parser_AST.level)
                    } in
                  (uu____4913, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4906 in
              {
                FStar_Parser_AST.tm = uu____4905;
                FStar_Parser_AST.range =
                  (uu___258_4904.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___258_4904.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4903
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4917; FStar_Ident.ident = uu____4918;
              FStar_Ident.nsstr = uu____4919; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4922; FStar_Ident.ident = uu____4923;
              FStar_Ident.nsstr = uu____4924; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4927; FStar_Ident.ident = uu____4928;
               FStar_Ident.nsstr = uu____4929; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4947 =
              let uu____4948 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4948 in
            mk1 uu____4947
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4949; FStar_Ident.ident = uu____4950;
              FStar_Ident.nsstr = uu____4951; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4954; FStar_Ident.ident = uu____4955;
              FStar_Ident.nsstr = uu____4956; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4959; FStar_Ident.ident = uu____4960;
              FStar_Ident.nsstr = uu____4961; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4966;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____4968 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4968 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4973 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4973))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4977 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4977 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Can only assign to mutable values",
                           (top.FStar_Parser_AST.range)))
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
                let uu____5004 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____5004 with
                | FStar_Pervasives_Native.Some uu____5013 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5018 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____5018 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5032 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5045 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____5045
              | uu____5046 ->
                  let uu____5053 =
                    let uu____5054 =
                      let uu____5059 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____5059, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5054 in
                  FStar_Exn.raise uu____5053))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5062 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5062 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5065 =
                    let uu____5066 =
                      let uu____5071 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5071, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5066 in
                  FStar_Exn.raise uu____5065
              | uu____5072 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5091 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5091 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5095 =
                    let uu____5102 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5102, true) in
                  (match uu____5095 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5117 ->
                            let uu____5124 =
                              FStar_Util.take
                                (fun uu____5148  ->
                                   match uu____5148 with
                                   | (uu____5153,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5124 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5217  ->
                                        match uu____5217 with
                                        | (t,imp) ->
                                            let te = desugar_term env t in
                                            arg_withimp_e imp te) args1 in
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1)) in
                                 let app =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2)) in
                                 if is_data
                                 then
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (app,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Data_app)))
                                 else app)))
              | FStar_Pervasives_Native.None  ->
                  let error_msg =
                    let uu____5260 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5260 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5263 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5270 =
              FStar_List.fold_left
                (fun uu____5315  ->
                   fun b  ->
                     match uu____5315 with
                     | (env1,tparams,typs) ->
                         let uu____5372 = desugar_binder env1 b in
                         (match uu____5372 with
                          | (xopt,t1) ->
                              let uu____5401 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5410 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5410)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5401 with
                               | (env2,x) ->
                                   let uu____5430 =
                                     let uu____5433 =
                                       let uu____5436 =
                                         let uu____5437 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5437 in
                                       [uu____5436] in
                                     FStar_List.append typs uu____5433 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___260_5463 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___260_5463.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___260_5463.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5430)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5270 with
             | (env1,uu____5487,targs) ->
                 let uu____5509 =
                   let uu____5514 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5514 in
                 (match uu____5509 with
                  | (tup,uu____5520) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5531 = uncurry binders t in
            (match uu____5531 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___227_5563 =
                   match uu___227_5563 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5577 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5577
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5599 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5599 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5614 = desugar_binder env b in
            (match uu____5614 with
             | (FStar_Pervasives_Native.None ,uu____5621) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5631 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5631 with
                  | ((x,uu____5637),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5644 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5644))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5664 =
              FStar_List.fold_left
                (fun uu____5684  ->
                   fun pat  ->
                     match uu____5684 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5710,t) ->
                              let uu____5712 =
                                let uu____5715 = free_type_vars env1 t in
                                FStar_List.append uu____5715 ftvs in
                              (env1, uu____5712)
                          | uu____5720 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5664 with
             | (uu____5725,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5737 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5737 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___228_5778 =
                   match uu___228_5778 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5816 =
                                 let uu____5817 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5817
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5816 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5870 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5870
                   | p::rest ->
                       let uu____5881 = desugar_binding_pat env1 p in
                       (match uu____5881 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5905 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5910 =
                              match b with
                              | LetBinder uu____5943 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____5993) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6029 =
                                          let uu____6034 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____6034, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____6029
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6070,uu____6071) ->
                                             let tup2 =
                                               let uu____6073 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6073
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6077 =
                                                 let uu____6080 =
                                                   let uu____6081 =
                                                     let uu____6096 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6099 =
                                                       let uu____6102 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6103 =
                                                         let uu____6106 =
                                                           let uu____6107 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6107 in
                                                         [uu____6106] in
                                                       uu____6102 ::
                                                         uu____6103 in
                                                     (uu____6096, uu____6099) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6081 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6080 in
                                               uu____6077
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6118 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6118 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6149,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6151,pats)) ->
                                             let tupn =
                                               let uu____6190 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6190
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6200 =
                                                 let uu____6201 =
                                                   let uu____6216 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6219 =
                                                     let uu____6228 =
                                                       let uu____6237 =
                                                         let uu____6238 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6238 in
                                                       [uu____6237] in
                                                     FStar_List.append args
                                                       uu____6228 in
                                                   (uu____6216, uu____6219) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6201 in
                                               mk1 uu____6200 in
                                             let p2 =
                                               let uu____6258 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6258 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6293 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5910 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6360,uu____6361,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6375 =
                let uu____6376 = unparen e in uu____6376.FStar_Parser_AST.tm in
              match uu____6375 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6382 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6386 ->
            let rec aux args e =
              let uu____6418 =
                let uu____6419 = unparen e in uu____6419.FStar_Parser_AST.tm in
              match uu____6418 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6432 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6432 in
                  aux (arg :: args) e1
              | uu____6445 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind1 =
              let uu____6471 =
                let uu____6472 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6472 in
              FStar_Parser_AST.mk_term uu____6471 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6473 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6473
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6476 =
              let uu____6477 =
                let uu____6484 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6484,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6477 in
            mk1 uu____6476
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6502 =
              let uu____6507 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6507 then desugar_typ else desugar_term in
            uu____6502 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6540 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6626  ->
                        match uu____6626 with
                        | (p,def) ->
                            let uu____6651 = is_app_pattern p in
                            if uu____6651
                            then
                              let uu____6670 =
                                destruct_app_pattern env top_level p in
                              (uu____6670, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6724 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6724, def1)
                               | uu____6753 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6779);
                                           FStar_Parser_AST.prange =
                                             uu____6780;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6804 =
                                            let uu____6819 =
                                              let uu____6824 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6824 in
                                            (uu____6819, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6804, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6871)
                                        ->
                                        if top_level
                                        then
                                          let uu____6894 =
                                            let uu____6909 =
                                              let uu____6914 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6914 in
                                            (uu____6909, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6894, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6960 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6979 =
                FStar_List.fold_left
                  (fun uu____7039  ->
                     fun uu____7040  ->
                       match (uu____7039, uu____7040) with
                       | ((env1,fnames,rec_bindings),((f,uu____7123,uu____7124),uu____7125))
                           ->
                           let uu____7204 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7230 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7230 with
                                  | (env2,xx) ->
                                      let uu____7249 =
                                        let uu____7252 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7252 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7249))
                             | FStar_Util.Inr l ->
                                 let uu____7260 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7260, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7204 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6979 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7386 =
                    match uu____7386 with
                    | ((uu____7409,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7453 = is_comp_type env1 t in
                                if uu____7453
                                then
                                  ((let uu____7455 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7465 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7465)) in
                                    match uu____7455 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7468 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7470 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7470))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7468
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7474 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7474 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7478 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7493 =
                                let uu____7494 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7494
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7493 in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1 in
                        mk_lb (lbname1, FStar_Syntax_Syntax.tun, body2) in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs in
                  let body1 = desugar_term env' body in
                  let uu____7528 =
                    let uu____7529 =
                      let uu____7542 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7542) in
                    FStar_Syntax_Syntax.Tm_let uu____7529 in
                  FStar_All.pipe_left mk1 uu____7528 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7573 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7573 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7600 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7600
                            FStar_Pervasives_Native.None in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t12
                                 }]), body1))
                    | LocalBinder (x,uu____7612) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7615;
                              FStar_Syntax_Syntax.p = uu____7616;_}::[] ->
                              body1
                          | uu____7621 ->
                              let uu____7624 =
                                let uu____7627 =
                                  let uu____7628 =
                                    let uu____7651 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7652 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7651, uu____7652) in
                                  FStar_Syntax_Syntax.Tm_match uu____7628 in
                                FStar_Syntax_Syntax.mk uu____7627 in
                              uu____7624 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7662 =
                          let uu____7663 =
                            let uu____7676 =
                              let uu____7677 =
                                let uu____7678 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7678] in
                              FStar_Syntax_Subst.close uu____7677 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7676) in
                          FStar_Syntax_Syntax.Tm_let uu____7663 in
                        FStar_All.pipe_left mk1 uu____7662 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____7704 = is_rec || (is_app_pattern pat) in
            if uu____7704
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____7713 =
                let uu____7714 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7714 in
              mk1 uu____7713 in
            let uu____7715 =
              let uu____7716 =
                let uu____7739 =
                  let uu____7742 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7742
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7763 =
                  let uu____7778 =
                    let uu____7791 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7794 = desugar_term env t2 in
                    (uu____7791, FStar_Pervasives_Native.None, uu____7794) in
                  let uu____7803 =
                    let uu____7818 =
                      let uu____7831 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7834 = desugar_term env t3 in
                      (uu____7831, FStar_Pervasives_Native.None, uu____7834) in
                    [uu____7818] in
                  uu____7778 :: uu____7803 in
                (uu____7739, uu____7763) in
              FStar_Syntax_Syntax.Tm_match uu____7716 in
            mk1 uu____7715
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____7975 =
              match uu____7975 with
              | (pat,wopt,b) ->
                  let uu____7993 = desugar_match_pat env pat in
                  (match uu____7993 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8014 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____8014 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____8016 =
              let uu____8017 =
                let uu____8040 = desugar_term env e in
                let uu____8041 = FStar_List.collect desugar_branch branches in
                (uu____8040, uu____8041) in
              FStar_Syntax_Syntax.Tm_match uu____8017 in
            FStar_All.pipe_left mk1 uu____8016
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8070 = is_comp_type env t in
              if uu____8070
              then
                let uu____8077 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8077
              else
                (let uu____8083 = desugar_term env t in
                 FStar_Util.Inl uu____8083) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8089 =
              let uu____8090 =
                let uu____8117 = desugar_term env e in
                (uu____8117, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8090 in
            FStar_All.pipe_left mk1 uu____8089
        | FStar_Parser_AST.Record (uu____8142,[]) ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8179 = FStar_List.hd fields in
              match uu____8179 with | (f,uu____8191) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8233  ->
                        match uu____8233 with
                        | (g,uu____8239) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8245,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8259 =
                         let uu____8260 =
                           let uu____8265 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8265, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8260 in
                       FStar_Exn.raise uu____8259
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level))) in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_ToSyntax_Env.constrname]) in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8273 =
                    let uu____8284 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8315  ->
                              match uu____8315 with
                              | (f,uu____8325) ->
                                  let uu____8326 =
                                    let uu____8327 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8327 in
                                  (uu____8326, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8284) in
                  FStar_Parser_AST.Construct uu____8273
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8345 =
                      let uu____8346 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8346 in
                    FStar_Parser_AST.mk_term uu____8345 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8348 =
                      let uu____8361 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8391  ->
                                match uu____8391 with
                                | (f,uu____8401) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8361) in
                    FStar_Parser_AST.Record uu____8348 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (x, FStar_Pervasives_Native.None))
                           x.FStar_Ident.idRange), e)],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let e = desugar_term env recterm1 in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8429;
                         FStar_Syntax_Syntax.vars = uu____8430;_},args);
                    FStar_Syntax_Syntax.pos = uu____8432;
                    FStar_Syntax_Syntax.vars = uu____8433;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8461 =
                     let uu____8462 =
                       let uu____8477 =
                         let uu____8478 =
                           let uu____8481 =
                             let uu____8482 =
                               let uu____8489 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8489) in
                             FStar_Syntax_Syntax.Record_ctor uu____8482 in
                           FStar_Pervasives_Native.Some uu____8481 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8478 in
                       (uu____8477, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8462 in
                   FStar_All.pipe_left mk1 uu____8461 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8520 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8524 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8524 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident in
                  let qual1 =
                    if is_rec
                    then
                      FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else FStar_Pervasives_Native.None in
                  let uu____8543 =
                    let uu____8544 =
                      let uu____8559 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8560 =
                        let uu____8563 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8563] in
                      (uu____8559, uu____8560) in
                    FStar_Syntax_Syntax.Tm_app uu____8544 in
                  FStar_All.pipe_left mk1 uu____8543))
        | FStar_Parser_AST.NamedTyp (uu____8568,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8571 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8572 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8573,uu____8574,uu____8575) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8588,uu____8589,uu____8590) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8603,uu____8604,uu____8605) ->
            failwith "Not implemented yet"
and not_ascribed: FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8619 -> false
    | uu____8628 -> true
and is_synth_by_tactic:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8634 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8634 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8638 -> false
and desugar_args:
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
           (fun uu____8675  ->
              match uu____8675 with
              | (a,imp) ->
                  let uu____8688 = desugar_term env a in
                  arg_withimp_e imp uu____8688))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = FStar_Exn.raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____8707 =
          match uu____8707 with
          | (t1,uu____8713) ->
              let uu____8714 =
                let uu____8715 = unparen t1 in uu____8715.FStar_Parser_AST.tm in
              (match uu____8714 with
               | FStar_Parser_AST.Requires uu____8716 -> true
               | uu____8723 -> false) in
        let is_ensures uu____8731 =
          match uu____8731 with
          | (t1,uu____8737) ->
              let uu____8738 =
                let uu____8739 = unparen t1 in uu____8739.FStar_Parser_AST.tm in
              (match uu____8738 with
               | FStar_Parser_AST.Ensures uu____8740 -> true
               | uu____8747 -> false) in
        let is_app head1 uu____8758 =
          match uu____8758 with
          | (t1,uu____8764) ->
              let uu____8765 =
                let uu____8766 = unparen t1 in uu____8766.FStar_Parser_AST.tm in
              (match uu____8765 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8768;
                      FStar_Parser_AST.level = uu____8769;_},uu____8770,uu____8771)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____8772 -> false) in
        let is_smt_pat uu____8780 =
          match uu____8780 with
          | (t1,uu____8786) ->
              let uu____8787 =
                let uu____8788 = unparen t1 in uu____8788.FStar_Parser_AST.tm in
              (match uu____8787 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8791);
                             FStar_Parser_AST.range = uu____8792;
                             FStar_Parser_AST.level = uu____8793;_},uu____8794)::uu____8795::[])
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
                             FStar_Parser_AST.range = uu____8834;
                             FStar_Parser_AST.level = uu____8835;_},uu____8836)::uu____8837::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____8862 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8890 = head_and_args t1 in
          match uu____8890 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing) in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None) in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let thunk_ens_ ens =
                     let wildpat =
                       FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                         ens.FStar_Parser_AST.range in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                   let thunk_ens uu____8984 =
                     match uu____8984 with
                     | (e,i) ->
                         let uu____8995 = thunk_ens_ e in (uu____8995, i) in
                   let fail_lemma uu____9005 =
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
                       "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"] in
                     let msg = FStar_String.concat "\n\t" expected_one_of in
                     FStar_Exn.raise
                       (FStar_Errors.Error
                          ((Prims.strcat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg), (t1.FStar_Parser_AST.range))) in
                   let args1 =
                     match args with
                     | [] -> fail_lemma ()
                     | req::[] when is_requires req -> fail_lemma ()
                     | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                     | dec::[] when is_decreases dec -> fail_lemma ()
                     | ens::[] ->
                         let uu____9085 =
                           let uu____9092 =
                             let uu____9099 = thunk_ens ens in
                             [uu____9099; nil_pat] in
                           req_true :: uu____9092 in
                         unit_tm :: uu____9085
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9146 =
                           let uu____9153 =
                             let uu____9160 = thunk_ens ens in
                             [uu____9160; nil_pat] in
                           req :: uu____9153 in
                         unit_tm :: uu____9146
                     | ens::smtpat::[] when
                         (((let uu____9209 = is_requires ens in
                            Prims.op_Negation uu____9209) &&
                             (let uu____9211 = is_smt_pat ens in
                              Prims.op_Negation uu____9211))
                            &&
                            (let uu____9213 = is_decreases ens in
                             Prims.op_Negation uu____9213))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9214 =
                           let uu____9221 =
                             let uu____9228 = thunk_ens ens in
                             [uu____9228; smtpat] in
                           req_true :: uu____9221 in
                         unit_tm :: uu____9214
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9275 =
                           let uu____9282 =
                             let uu____9289 = thunk_ens ens in
                             [uu____9289; nil_pat; dec] in
                           req_true :: uu____9282 in
                         unit_tm :: uu____9275
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9349 =
                           let uu____9356 =
                             let uu____9363 = thunk_ens ens in
                             [uu____9363; smtpat; dec] in
                           req_true :: uu____9356 in
                         unit_tm :: uu____9349
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9423 =
                           let uu____9430 =
                             let uu____9437 = thunk_ens ens in
                             [uu____9437; nil_pat; dec] in
                           req :: uu____9430 in
                         unit_tm :: uu____9423
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9497 =
                           let uu____9504 =
                             let uu____9511 = thunk_ens ens in
                             [uu____9511; smtpat] in
                           req :: uu____9504 in
                         unit_tm :: uu____9497
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9576 =
                           let uu____9583 =
                             let uu____9590 = thunk_ens ens in
                             [uu____9590; dec; smtpat] in
                           req :: uu____9583 in
                         unit_tm :: uu____9576
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9652 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9652, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9680 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9680
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9698 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9698
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
               | uu____9736 ->
                   let default_effect =
                     let uu____9738 = FStar_Options.ml_ish () in
                     if uu____9738
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9741 =
                           FStar_Options.warn_default_effects () in
                         if uu____9741
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9765 = pre_process_comp_typ t in
        match uu____9765 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9814 =
                  let uu____9815 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9815 in
                fail uu____9814)
             else ();
             (let is_universe uu____9824 =
                match uu____9824 with
                | (uu____9829,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9831 = FStar_Util.take is_universe args in
              match uu____9831 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9890  ->
                         match uu____9890 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9897 =
                    let uu____9912 = FStar_List.hd args1 in
                    let uu____9921 = FStar_List.tl args1 in
                    (uu____9912, uu____9921) in
                  (match uu____9897 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9976 =
                         let is_decrease uu____10012 =
                           match uu____10012 with
                           | (t1,uu____10022) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10032;
                                       FStar_Syntax_Syntax.vars = uu____10033;_},uu____10034::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10065 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9976 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10179  ->
                                      match uu____10179 with
                                      | (t1,uu____10189) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10198,(arg,uu____10200)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10229 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10243 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1) in
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
                                (let flags =
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
                                         else [] in
                                 let flags1 =
                                   FStar_List.append flags cattributes in
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
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10391 -> pat in
                                         let uu____10392 =
                                           let uu____10403 =
                                             let uu____10414 =
                                               let uu____10423 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10423, aq) in
                                             [uu____10414] in
                                           ens :: uu____10403 in
                                         req :: uu____10392
                                     | uu____10464 -> rest2
                                   else rest2 in
                                 FStar_Syntax_Syntax.mk_Comp
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_name = eff;
                                     FStar_Syntax_Syntax.result_typ =
                                       result_typ;
                                     FStar_Syntax_Syntax.effect_args = rest3;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags1
                                          decreases_clause)
                                   })))))
and desugar_formula:
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
        | uu____10486 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___261_10503 = t in
        {
          FStar_Syntax_Syntax.n = (uu___261_10503.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___261_10503.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___262_10537 = b in
             {
               FStar_Parser_AST.b = (uu___262_10537.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___262_10537.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___262_10537.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10596 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10596)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10609 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10609 with
             | (env1,a1) ->
                 let a2 =
                   let uu___263_10619 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___263_10619.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___263_10619.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10641 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10655 =
                     let uu____10658 =
                       let uu____10659 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10659] in
                     no_annot_abs uu____10658 body2 in
                   FStar_All.pipe_left setpos uu____10655 in
                 let uu____10664 =
                   let uu____10665 =
                     let uu____10680 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10681 =
                       let uu____10684 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10684] in
                     (uu____10680, uu____10681) in
                   FStar_Syntax_Syntax.Tm_app uu____10665 in
                 FStar_All.pipe_left mk1 uu____10664)
        | uu____10689 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____10761 = q (rest, pats, body) in
              let uu____10768 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10761 uu____10768
                FStar_Parser_AST.Formula in
            let uu____10769 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10769 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10778 -> failwith "impossible" in
      let uu____10781 =
        let uu____10782 = unparen f in uu____10782.FStar_Parser_AST.tm in
      match uu____10781 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10789,uu____10790) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10801,uu____10802) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10833 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10833
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10869 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10869
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____10912 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      let uu____10917 =
        FStar_List.fold_left
          (fun uu____10953  ->
             fun b  ->
               match uu____10953 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___264_11005 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___264_11005.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___264_11005.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___264_11005.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11022 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____11022 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___265_11042 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___265_11042.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___265_11042.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11059 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10917 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11146 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11146)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11151 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11151)
      | FStar_Parser_AST.TVariable x ->
          let uu____11155 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11155)
      | FStar_Parser_AST.NoName t ->
          let uu____11163 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11163)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators:
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
               (fun uu___229_11199  ->
                  match uu___229_11199 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11200 -> false)) in
        let quals2 q =
          let uu____11211 =
            (let uu____11214 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11214) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11211
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11227 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11227;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
let mk_indexed_projector_names:
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
            let p = FStar_Ident.range_of_lid lid in
            let uu____11263 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11293  ->
                        match uu____11293 with
                        | (x,uu____11301) ->
                            let uu____11302 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11302 with
                             | (field_name,uu____11310) ->
                                 let only_decl =
                                   ((let uu____11314 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11314)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11316 =
                                        let uu____11317 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11317.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11316) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11331 =
                                       FStar_List.filter
                                         (fun uu___230_11335  ->
                                            match uu___230_11335 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11336 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11331
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___231_11349  ->
                                             match uu___231_11349 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11350 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
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
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11358 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11358
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11363 =
                                        let uu____11368 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11368 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11363;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11370 =
                                        let uu____11371 =
                                          let uu____11378 =
                                            let uu____11381 =
                                              let uu____11382 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11382
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11381] in
                                          ((false, [lb]), uu____11378) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11371 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11370;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11263 FStar_List.flatten
let mk_data_projector_names:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11429,t,uu____11431,n1,uu____11433) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11438 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11438 with
             | (formals,uu____11454) ->
                 (match formals with
                  | [] -> []
                  | uu____11477 ->
                      let filter_records uu___232_11489 =
                        match uu___232_11489 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11492,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11504 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11506 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11506 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11516 = FStar_Util.first_N n1 formals in
                      (match uu____11516 with
                       | (uu____11539,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11565 -> []
let mk_typ_abbrev:
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
                    let uu____11623 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11623
                    then
                      let uu____11626 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11626
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11629 =
                      let uu____11634 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11634 in
                    let uu____11635 =
                      let uu____11638 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11638 in
                    let uu____11641 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11629;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11635;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11641
                    } in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
let rec desugar_tycon:
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
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___233_11690 =
            match uu___233_11690 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11692,uu____11693) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11703,uu____11704,uu____11705) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11715,uu____11716,uu____11717) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____11747,uu____11748,uu____11749) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11791) ->
                let uu____11792 =
                  let uu____11793 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11793 in
                FStar_Parser_AST.mk_term uu____11792 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11795 =
                  let uu____11796 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11796 in
                FStar_Parser_AST.mk_term uu____11795 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11798) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____11821 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11827 =
                     let uu____11828 =
                       let uu____11835 = binder_to_term b in
                       (out, uu____11835, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11828 in
                   FStar_Parser_AST.mk_term uu____11827
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___234_11845 =
            match uu___234_11845 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____11900  ->
                       match uu____11900 with
                       | (x,t,uu____11911) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____11917 =
                    let uu____11918 =
                      let uu____11919 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11919 in
                    FStar_Parser_AST.mk_term uu____11918
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11917 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11923 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11950  ->
                          match uu____11950 with
                          | (x,uu____11960,uu____11961) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____11923)
            | uu____12014 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___235_12045 =
            match uu___235_12045 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____12069 = typars_of_binders _env binders in
                (match uu____12069 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12115 =
                         let uu____12116 =
                           let uu____12117 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12117 in
                         FStar_Parser_AST.mk_term uu____12116
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12115 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
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
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____12130 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12174 =
              FStar_List.fold_left
                (fun uu____12214  ->
                   fun uu____12215  ->
                     match (uu____12214, uu____12215) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12306 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12306 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12174 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12419 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12419
                | uu____12420 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12428 = desugar_abstract_tc quals env [] tc in
              (match uu____12428 with
               | (uu____12441,uu____12442,se,uu____12444) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12447,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12464 =
                                 let uu____12465 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12465 in
                               if uu____12464
                               then
                                 let uu____12466 =
                                   let uu____12467 =
                                     FStar_Syntax_Print.lid_to_string l in
                                   FStar_Util.format1
                                     "Adding an implicit 'assume new' qualifier on %s"
                                     uu____12467 in
                                 FStar_Errors.warn
                                   se.FStar_Syntax_Syntax.sigrng uu____12466
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12474 ->
                               let uu____12475 =
                                 let uu____12478 =
                                   let uu____12479 =
                                     let uu____12492 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12492) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12479 in
                                 FStar_Syntax_Syntax.mk uu____12478 in
                               uu____12475 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___266_12496 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___266_12496.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___266_12496.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___266_12496.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12499 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12502 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12502
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12517 = typars_of_binders env binders in
              (match uu____12517 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12553 =
                           FStar_Util.for_some
                             (fun uu___236_12555  ->
                                match uu___236_12555 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12556 -> false) quals in
                         if uu____12553
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12563 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___237_12567  ->
                               match uu___237_12567 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12568 -> false)) in
                     if uu____12563
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12577 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12577
                     then
                       let uu____12580 =
                         let uu____12587 =
                           let uu____12588 = unparen t in
                           uu____12588.FStar_Parser_AST.tm in
                         match uu____12587 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12609 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12639)::args_rev ->
                                   let uu____12651 =
                                     let uu____12652 = unparen last_arg in
                                     uu____12652.FStar_Parser_AST.tm in
                                   (match uu____12651 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12680 -> ([], args))
                               | uu____12689 -> ([], args) in
                             (match uu____12609 with
                              | (cattributes,args1) ->
                                  let uu____12728 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12728))
                         | uu____12739 -> (t, []) in
                       match uu____12580 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___238_12761  ->
                                     match uu___238_12761 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____12762 -> true)) in
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
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____12773)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12797 = tycon_record_as_variant trec in
              (match uu____12797 with
               | (t,fs) ->
                   let uu____12814 =
                     let uu____12817 =
                       let uu____12818 =
                         let uu____12827 =
                           let uu____12830 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12830 in
                         (uu____12827, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12818 in
                     uu____12817 :: quals in
                   desugar_tycon env d uu____12814 [t])
          | uu____12835::uu____12836 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____12997 = et in
                match uu____12997 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13222 ->
                         let trec = tc in
                         let uu____13246 = tycon_record_as_variant trec in
                         (match uu____13246 with
                          | (t,fs) ->
                              let uu____13305 =
                                let uu____13308 =
                                  let uu____13309 =
                                    let uu____13318 =
                                      let uu____13321 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13321 in
                                    (uu____13318, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13309 in
                                uu____13308 :: quals1 in
                              collect_tcs uu____13305 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13408 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13408 with
                          | (env2,uu____13468,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13617 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13617 with
                          | (env2,uu____13677,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13802 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13849 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13849 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___240_14360  ->
                             match uu___240_14360 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14427,uu____14428);
                                    FStar_Syntax_Syntax.sigrng = uu____14429;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14430;
                                    FStar_Syntax_Syntax.sigmeta = uu____14431;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14432;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14493 =
                                     typars_of_binders env1 binders in
                                   match uu____14493 with
                                   | (env2,tpars1) ->
                                       let uu____14524 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14524 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14557 =
                                   let uu____14578 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14578) in
                                 [uu____14557]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14646);
                                    FStar_Syntax_Syntax.sigrng = uu____14647;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14649;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14650;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____14746 = push_tparams env1 tpars in
                                 (match uu____14746 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14823  ->
                                             match uu____14823 with
                                             | (x,uu____14837) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14845 =
                                        let uu____14874 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____14988  ->
                                                  match uu____14988 with
                                                  | (id,topt,doc1,of_notation)
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
                                                               t -> t) in
                                                      let t1 =
                                                        let uu____15044 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____15044 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___239_15055
                                                                 ->
                                                                match uu___239_15055
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15067
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____15075 =
                                                        let uu____15096 =
                                                          let uu____15097 =
                                                            let uu____15098 =
                                                              let uu____15113
                                                                =
                                                                let uu____15116
                                                                  =
                                                                  let uu____15119
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15119 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15116 in
                                                              (name, univs1,
                                                                uu____15113,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15098 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15097;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____15096) in
                                                      (name, uu____15075))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14874 in
                                      (match uu____14845 with
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
                             | uu____15358 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15490  ->
                             match uu____15490 with
                             | (name_doc,uu____15518,uu____15519) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15599  ->
                             match uu____15599 with
                             | (uu____15620,uu____15621,se) -> se)) in
                   let uu____15651 =
                     let uu____15658 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15658 rng in
                   (match uu____15651 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____15724  ->
                                  match uu____15724 with
                                  | (uu____15747,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15798,tps,k,uu____15801,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1 in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____15820 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15837  ->
                                 match uu____15837 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
let desugar_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      let uu____15874 =
        FStar_List.fold_left
          (fun uu____15897  ->
             fun b  ->
               match uu____15897 with
               | (env1,binders1) ->
                   let uu____15917 = desugar_binder env1 b in
                   (match uu____15917 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15934 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15934 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15951 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____15874 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let rec desugar_effect:
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
                let env0 = env in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____16069 = desugar_binders monad_env eff_binders in
                match uu____16069 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16090 =
                        let uu____16091 =
                          let uu____16098 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16098 in
                        FStar_List.length uu____16091 in
                      uu____16090 = (Prims.parse_int "1") in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"] in
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
                          "trivial"] in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____16140,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16142,uu____16143,uu____16144),uu____16145)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16178 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16179 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16191 = name_of_eff_decl decl in
                           FStar_List.mem uu____16191 mandatory_members)
                        eff_decls in
                    (match uu____16179 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16208 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16237  ->
                                   fun decl  ->
                                     match uu____16237 with
                                     | (env2,out) ->
                                         let uu____16257 =
                                           desugar_decl env2 decl in
                                         (match uu____16257 with
                                          | (env3,ses) ->
                                              let uu____16270 =
                                                let uu____16273 =
                                                  FStar_List.hd ses in
                                                uu____16273 :: out in
                                              (env3, uu____16270)))
                                (env1, [])) in
                         (match uu____16208 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16341,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16344,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16345,
                                                                (def,uu____16347)::
                                                                (cps_type,uu____16349)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16350;
                                                             FStar_Parser_AST.level
                                                               = uu____16351;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16403 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16403 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16423 =
                                                   let uu____16424 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16425 =
                                                     let uu____16426 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16426 in
                                                   let uu____16431 =
                                                     let uu____16432 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16432 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16424;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16425;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16431
                                                   } in
                                                 (uu____16423, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16439,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16442,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16477 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16477 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16497 =
                                                   let uu____16498 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16499 =
                                                     let uu____16500 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16500 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16498;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16499;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16497, doc1))
                                        | uu____16507 ->
                                            FStar_Exn.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let actions1 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  actions_docs in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____16537 =
                                  let uu____16538 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16538 in
                                ([], uu____16537) in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (FStar_Pervasives_Native.Some mname))
                                  quals in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____16555 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16555) in
                                  let uu____16562 =
                                    let uu____16563 =
                                      let uu____16564 =
                                        let uu____16565 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16565 in
                                      let uu____16574 = lookup "return" in
                                      let uu____16575 = lookup "bind" in
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
                                          uu____16564;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16574;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16575;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16563 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16562;
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
                                       (fun uu___241_16579  ->
                                          match uu___241_16579 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16580 -> true
                                          | uu____16581 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16591 =
                                     let uu____16592 =
                                       let uu____16593 = lookup "return_wp" in
                                       let uu____16594 = lookup "bind_wp" in
                                       let uu____16595 =
                                         lookup "if_then_else" in
                                       let uu____16596 = lookup "ite_wp" in
                                       let uu____16597 = lookup "stronger" in
                                       let uu____16598 = lookup "close_wp" in
                                       let uu____16599 = lookup "assert_p" in
                                       let uu____16600 = lookup "assume_p" in
                                       let uu____16601 = lookup "null_wp" in
                                       let uu____16602 = lookup "trivial" in
                                       let uu____16603 =
                                         if rr
                                         then
                                           let uu____16604 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16604
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16620 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16622 =
                                         if rr then lookup "bind" else un_ts in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16593;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16594;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16595;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16596;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16597;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16598;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16599;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16600;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16601;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16602;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16603;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16620;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16622;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16592 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16591;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }) in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____16647  ->
                                          match uu____16647 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16661 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16661 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16663 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16663
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env) in
                                  let quals1 =
                                    [FStar_Syntax_Syntax.Assumption;
                                    FStar_Syntax_Syntax.Reflectable mname] in
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
                                    } in
                                  FStar_ToSyntax_Env.push_sigelt env5
                                    refl_decl
                                else env5 in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc in
                              (env7, [se])))
and desugar_redefine_effect:
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
                let env0 = env in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____16694 = desugar_binders env1 eff_binders in
                match uu____16694 with
                | (env2,binders) ->
                    let uu____16713 =
                      let uu____16732 = head_and_args defn in
                      match uu____16732 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16777 ->
                                let uu____16778 =
                                  let uu____16779 =
                                    let uu____16784 =
                                      let uu____16785 =
                                        let uu____16786 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____16786 " not found" in
                                      Prims.strcat "Effect " uu____16785 in
                                    (uu____16784,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16779 in
                                FStar_Exn.raise uu____16778 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16788 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16818)::args_rev ->
                                let uu____16830 =
                                  let uu____16831 = unparen last_arg in
                                  uu____16831.FStar_Parser_AST.tm in
                                (match uu____16830 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16859 -> ([], args))
                            | uu____16868 -> ([], args) in
                          (match uu____16788 with
                           | (cattributes,args1) ->
                               let uu____16919 = desugar_args env2 args1 in
                               let uu____16928 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16919, uu____16928)) in
                    (match uu____16713 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____16987 =
                           match uu____16987 with
                           | (uu____17000,x) ->
                               let uu____17006 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____17006 with
                                | (edb,x1) ->
                                    (if
                                       (FStar_List.length args) <>
                                         (FStar_List.length edb)
                                     then
                                       FStar_Exn.raise
                                         (FStar_Errors.Error
                                            ("Unexpected number of arguments to effect constructor",
                                              (defn.FStar_Parser_AST.range)))
                                     else ();
                                     (let s =
                                        FStar_Syntax_Util.subst_of_list edb
                                          args in
                                      let uu____17032 =
                                        let uu____17033 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____17033 in
                                      ([], uu____17032)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____17038 =
                             let uu____17039 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____17039 in
                           let uu____17050 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17051 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17052 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17053 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17054 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____17055 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17056 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17057 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17058 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17059 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____17060 =
                             let uu____17061 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____17061 in
                           let uu____17072 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17073 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17074 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____17082 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____17083 =
                                    let uu____17084 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____17084 in
                                  let uu____17095 =
                                    let uu____17096 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____17096 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____17082;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____17083;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____17095
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____17038;
                             FStar_Syntax_Syntax.ret_wp = uu____17050;
                             FStar_Syntax_Syntax.bind_wp = uu____17051;
                             FStar_Syntax_Syntax.if_then_else = uu____17052;
                             FStar_Syntax_Syntax.ite_wp = uu____17053;
                             FStar_Syntax_Syntax.stronger = uu____17054;
                             FStar_Syntax_Syntax.close_wp = uu____17055;
                             FStar_Syntax_Syntax.assert_p = uu____17056;
                             FStar_Syntax_Syntax.assume_p = uu____17057;
                             FStar_Syntax_Syntax.null_wp = uu____17058;
                             FStar_Syntax_Syntax.trivial = uu____17059;
                             FStar_Syntax_Syntax.repr = uu____17060;
                             FStar_Syntax_Syntax.return_repr = uu____17072;
                             FStar_Syntax_Syntax.bind_repr = uu____17073;
                             FStar_Syntax_Syntax.actions = uu____17074
                           } in
                         let se =
                           let for_free =
                             let uu____17109 =
                               let uu____17110 =
                                 let uu____17117 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____17117 in
                               FStar_List.length uu____17110 in
                             uu____17109 = (Prims.parse_int "1") in
                           let uu____17146 =
                             let uu____17149 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____17149 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____17146;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           } in
                         let monad_env = env2 in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se in
                         let env4 =
                           FStar_ToSyntax_Env.push_doc env3 ed_lid
                             d.FStar_Parser_AST.doc in
                         let env5 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env5  ->
                                   fun a  ->
                                     let doc1 =
                                       FStar_ToSyntax_Env.try_lookup_doc env5
                                         a.FStar_Syntax_Syntax.action_name in
                                     let env6 =
                                       let uu____17169 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____17169 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____17171 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____17171
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env) in
                             let quals1 =
                               [FStar_Syntax_Syntax.Assumption;
                               FStar_Syntax_Syntax.Reflectable mname] in
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
                               } in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5 in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc in
                         (env7, [se]))
and mk_comment_attr:
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun d  ->
    let uu____17186 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____17186 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17237 ->
              let uu____17238 =
                let uu____17239 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17239 in
              Prims.strcat "\n  " uu____17238
          | uu____17240 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____17253  ->
               match uu____17253 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else "" in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)) in
        let fv =
          let uu____17271 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____17271
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____17273 =
          let uu____17282 = FStar_Syntax_Syntax.as_arg arg in [uu____17282] in
        FStar_Syntax_Util.mk_app fv uu____17273
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17289 = desugar_decl_noattrs env d in
      match uu____17289 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____17309 = mk_comment_attr d in uu____17309 :: attrs1 in
          let uu____17314 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___267_17320 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___267_17320.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___267_17320.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___267_17320.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___267_17320.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____17314)
and desugar_decl_noattrs:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
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
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17346 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17362 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17362, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17401  ->
                 match uu____17401 with | (x,uu____17409) -> x) tcs in
          let uu____17414 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17414 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17436;
                    FStar_Parser_AST.prange = uu____17437;_},uu____17438)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17447;
                    FStar_Parser_AST.prange = uu____17448;_},uu____17449)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17464;
                         FStar_Parser_AST.prange = uu____17465;_},uu____17466);
                    FStar_Parser_AST.prange = uu____17467;_},uu____17468)::[]
                   -> false
               | (p,uu____17484)::[] ->
                   let uu____17493 = is_app_pattern p in
                   Prims.op_Negation uu____17493
               | uu____17494 -> false) in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
            let ds_lets = desugar_term_maybe_top true env as_inner_let in
            let uu____17513 =
              let uu____17514 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17514.FStar_Syntax_Syntax.n in
            (match uu____17513 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17522) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17555::uu____17556 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17559 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___242_17572  ->
                               match uu___242_17572 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17575;
                                   FStar_Syntax_Syntax.lbunivs = uu____17576;
                                   FStar_Syntax_Syntax.lbtyp = uu____17577;
                                   FStar_Syntax_Syntax.lbeff = uu____17578;
                                   FStar_Syntax_Syntax.lbdef = uu____17579;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17587;
                                   FStar_Syntax_Syntax.lbtyp = uu____17588;
                                   FStar_Syntax_Syntax.lbeff = uu____17589;
                                   FStar_Syntax_Syntax.lbdef = uu____17590;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17600 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17614  ->
                             match uu____17614 with
                             | (uu____17619,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17600
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17631 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17631
                   then
                     let uu____17640 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___268_17654 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___269_17656 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___269_17656.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___269_17656.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___268_17654.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___268_17654.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___268_17654.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___268_17654.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17640)
                   else lbs in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = []
                   } in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names1 in
                 (env2, [s])
             | uu____17688 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17694 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17713 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17694 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___270_17737 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___270_17737.FStar_Parser_AST.prange)
                       }
                   | uu____17738 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___271_17745 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___271_17745.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___271_17745.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___271_17745.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17777 id =
                   match uu____17777 with
                   | (env1,ses) ->
                       let main =
                         let uu____17798 =
                           let uu____17799 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17799 in
                         FStar_Parser_AST.mk_term uu____17798
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id] in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____17849 = desugar_decl env1 id_decl in
                       (match uu____17849 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17867 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17867 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc in
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
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____17898 = close_fun env t in desugar_term env uu____17898 in
          let quals1 =
            let uu____17902 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17902
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____17908 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17908;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17920 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____17920 with
           | (t,uu____17934) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
               let data_ops = mk_data_projector_names [] env2 se in
               let discs = mk_data_discriminators [] env2 [l] in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____17968 =
              let uu____17975 = FStar_Syntax_Syntax.null_binder t in
              [uu____17975] in
            let uu____17976 =
              let uu____17979 =
                let uu____17980 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17980 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17979 in
            FStar_Syntax_Util.arrow uu____17968 uu____17976 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
          let data_ops = mk_data_projector_names [] env2 se in
          let discs = mk_data_discriminators [] env2 [l] in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
              (FStar_List.append discs data_ops) in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____18042 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____18042 with
            | FStar_Pervasives_Native.None  ->
                let uu____18045 =
                  let uu____18046 =
                    let uu____18051 =
                      let uu____18052 =
                        let uu____18053 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____18053 " not found" in
                      Prims.strcat "Effect name " uu____18052 in
                    (uu____18051, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____18046 in
                FStar_Exn.raise uu____18045
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____18057 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18099 =
                  let uu____18108 =
                    let uu____18115 = desugar_term env t in ([], uu____18115) in
                  FStar_Pervasives_Native.Some uu____18108 in
                (uu____18099, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18148 =
                  let uu____18157 =
                    let uu____18164 = desugar_term env wp in
                    ([], uu____18164) in
                  FStar_Pervasives_Native.Some uu____18157 in
                let uu____18173 =
                  let uu____18182 =
                    let uu____18189 = desugar_term env t in ([], uu____18189) in
                  FStar_Pervasives_Native.Some uu____18182 in
                (uu____18148, uu____18173)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18215 =
                  let uu____18224 =
                    let uu____18231 = desugar_term env t in ([], uu____18231) in
                  FStar_Pervasives_Native.Some uu____18224 in
                (FStar_Pervasives_Native.None, uu____18215) in
          (match uu____18057 with
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
                 } in
               (env, [se]))
let desugar_decls:
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun decls  ->
      let uu____18321 =
        FStar_List.fold_left
          (fun uu____18341  ->
             fun d  ->
               match uu____18341 with
               | (env1,sigelts) ->
                   let uu____18361 = desugar_decl env1 d in
                   (match uu____18361 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____18321 with
      | (env1,sigelts) ->
          let rec forward acc uu___244_18402 =
            match uu___244_18402 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18416,FStar_Syntax_Syntax.Sig_let uu____18417) ->
                     let uu____18430 =
                       let uu____18433 =
                         let uu___272_18434 = se2 in
                         let uu____18435 =
                           let uu____18438 =
                             FStar_List.filter
                               (fun uu___243_18452  ->
                                  match uu___243_18452 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18456;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18457;_},uu____18458);
                                      FStar_Syntax_Syntax.pos = uu____18459;
                                      FStar_Syntax_Syntax.vars = uu____18460;_}
                                      when
                                      let uu____18483 =
                                        let uu____18484 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____18484 in
                                      uu____18483 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18485 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____18438
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___272_18434.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___272_18434.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___272_18434.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___272_18434.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18435
                         } in
                       uu____18433 :: se1 :: acc in
                     forward uu____18430 sigelts1
                 | uu____18490 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____18498 = forward [] sigelts in (env1, uu____18498)
let open_prims_all:
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
let desugar_modul_common:
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
          | (FStar_Pervasives_Native.None ,uu____18552) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18556;
               FStar_Syntax_Syntax.exports = uu____18557;
               FStar_Syntax_Syntax.is_interface = uu____18558;_},FStar_Parser_AST.Module
             (current_lid,uu____18560)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18568) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18571 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18607 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18607, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18624 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18624, mname, decls, false) in
        match uu____18571 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18654 = desugar_decls env2 decls in
            (match uu____18654 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   } in
                 (env3, modul, pop_when_done))
let as_interface: FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
let desugar_partial_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____18712 =
            (FStar_Options.interactive ()) &&
              (let uu____18714 =
                 let uu____18715 =
                   let uu____18716 = FStar_Options.file_list () in
                   FStar_List.hd uu____18716 in
                 FStar_Util.get_file_extension uu____18715 in
               FStar_List.mem uu____18714 ["fsti"; "fsi"]) in
          if uu____18712 then as_interface m else m in
        let uu____18720 = desugar_modul_common curmod env m1 in
        match uu____18720 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18735 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18753 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18753 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18769 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18769
            then
              let uu____18770 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18770
            else ());
           (let uu____18772 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18772, modul)))
let ast_modul_to_modul:
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____18787 = desugar_modul env modul in
      match uu____18787 with | (env1,modul1) -> (modul1, env1)
let decls_to_sigelts:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____18815 = desugar_decls env decls in
      match uu____18815 with | (env1,sigelts) -> (sigelts, env1)
let partial_ast_modul_to_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____18855 = desugar_partial_modul modul env a_modul in
        match uu____18855 with | (env1,modul1) -> (modul1, env1)
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun m  ->
    fun mii  ->
      fun en  ->
        let uu____18883 =
          FStar_ToSyntax_Env.prepare_module_or_interface false false en
            m.FStar_Syntax_Syntax.name mii in
        match uu____18883 with
        | (en1,pop_when_done) ->
            let en2 =
              let uu____18895 =
                FStar_ToSyntax_Env.set_current_module en1
                  m.FStar_Syntax_Syntax.name in
              FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18895
                m.FStar_Syntax_Syntax.exports in
            let env = FStar_ToSyntax_Env.finish en2 m in
            let uu____18897 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  m.FStar_Syntax_Syntax.name env
              else env in
            ((), uu____18897)