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
  fun uu___209_62  ->
    match uu___209_62 with
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
      fun uu___210_83  ->
        match uu___210_83 with
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
  fun uu___211_91  ->
    match uu___211_91 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___212_101  ->
    match uu___212_101 with
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
  fun uu___213_1455  ->
    match uu___213_1455 with
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
      fun uu___214_1490  ->
        match uu___214_1490 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1506 = FStar_Syntax_Syntax.null_binder k in
            (uu____1506, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1511 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1511 with
             | (env1,a1) ->
                 (((let uu___237_1531 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___237_1531.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___237_1531.FStar_Syntax_Syntax.index);
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
  fun uu___215_1834  ->
    match uu___215_1834 with
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
                  (fun uu___216_2042  ->
                     match uu___216_2042 with
                     | FStar_Util.Inr uu____2047 -> true
                     | uu____2048 -> false) univargs
              then
                let uu____2053 =
                  let uu____2054 =
                    FStar_List.map
                      (fun uu___217_2063  ->
                         match uu___217_2063 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2054 in
                FStar_Util.Inr uu____2053
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___218_2080  ->
                        match uu___218_2080 with
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
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2604 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2620 =
                 let uu____2621 =
                   let uu____2622 =
                     let uu____2629 =
                       let uu____2630 =
                         let uu____2635 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2635, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2630 in
                     (uu____2629, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2622 in
                 {
                   FStar_Parser_AST.pat = uu____2621;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2620
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2640 = aux loc env1 p2 in
               (match uu____2640 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____2675 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2683 = close_fun env1 t in
                            desugar_term env1 uu____2683 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2685 -> true)
                           then
                             (let uu____2686 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2687 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2688 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____2686 uu____2687 uu____2688)
                           else ();
                           LocalBinder
                             (((let uu___238_2691 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___238_2691.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___238_2691.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2695 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2695, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2706 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2706, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2727 = resolvex loc env1 x in
               (match uu____2727 with
                | (loc1,env2,xbv) ->
                    let uu____2749 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2749, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2770 = resolvex loc env1 x in
               (match uu____2770 with
                | (loc1,env2,xbv) ->
                    let uu____2792 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2792, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2804 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2804, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2828;_},args)
               ->
               let uu____2834 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2875  ->
                        match uu____2875 with
                        | (loc1,env2,args1) ->
                            let uu____2923 = aux loc1 env2 arg in
                            (match uu____2923 with
                             | (loc2,env3,uu____2952,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2834 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3022 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3022, false))
           | FStar_Parser_AST.PatApp uu____3039 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3061 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3094  ->
                        match uu____3094 with
                        | (loc1,env2,pats1) ->
                            let uu____3126 = aux loc1 env2 pat in
                            (match uu____3126 with
                             | (loc2,env3,uu____3151,pat1,uu____3153) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3061 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3196 =
                        let uu____3199 =
                          let uu____3204 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3204 in
                        let uu____3205 =
                          let uu____3206 =
                            let uu____3219 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3219, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3206 in
                        FStar_All.pipe_left uu____3199 uu____3205 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3251 =
                               let uu____3252 =
                                 let uu____3265 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3265, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3252 in
                             FStar_All.pipe_left (pos_r r) uu____3251) pats1
                        uu____3196 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3309 =
                 FStar_List.fold_left
                   (fun uu____3349  ->
                      fun p2  ->
                        match uu____3349 with
                        | (loc1,env2,pats) ->
                            let uu____3398 = aux loc1 env2 p2 in
                            (match uu____3398 with
                             | (loc2,env3,uu____3427,pat,uu____3429) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3309 with
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
                    let uu____3524 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3524 with
                     | (constr,uu____3546) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3549 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3551 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3551, false)))
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
                      (fun uu____3622  ->
                         match uu____3622 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3652  ->
                         match uu____3652 with
                         | (f,uu____3658) ->
                             let uu____3659 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3685  ->
                                       match uu____3685 with
                                       | (g,uu____3691) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3659 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3696,p2)
                                  -> p2))) in
               let app =
                 let uu____3703 =
                   let uu____3704 =
                     let uu____3711 =
                       let uu____3712 =
                         let uu____3713 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3713 in
                       FStar_Parser_AST.mk_pattern uu____3712
                         p1.FStar_Parser_AST.prange in
                     (uu____3711, args) in
                   FStar_Parser_AST.PatApp uu____3704 in
                 FStar_Parser_AST.mk_pattern uu____3703
                   p1.FStar_Parser_AST.prange in
               let uu____3716 = aux loc env1 app in
               (match uu____3716 with
                | (env2,e,b,p2,uu____3745) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3773 =
                            let uu____3774 =
                              let uu____3787 =
                                let uu___239_3788 = fv in
                                let uu____3789 =
                                  let uu____3792 =
                                    let uu____3793 =
                                      let uu____3800 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3800) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3793 in
                                  FStar_Pervasives_Native.Some uu____3792 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___239_3788.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___239_3788.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3789
                                } in
                              (uu____3787, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3774 in
                          FStar_All.pipe_left pos uu____3773
                      | uu____3827 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3874 = aux loc env1 p2 in
               (match uu____3874 with
                | (loc1,env2,var,p3,uu____3901) ->
                    let uu____3906 =
                      FStar_List.fold_left
                        (fun uu____3938  ->
                           fun p4  ->
                             match uu____3938 with
                             | (loc2,env3,ps1) ->
                                 let uu____3971 = aux loc2 env3 p4 in
                                 (match uu____3971 with
                                  | (loc3,env4,uu____3996,p5,uu____3998) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____3906 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4049 ->
               let uu____4050 = aux loc env1 p1 in
               (match uu____4050 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4090 = aux_maybe_or env p in
         match uu____4090 with
         | (env1,b,pats) ->
             ((let uu____4121 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4121);
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
            let uu____4156 =
              let uu____4157 =
                let uu____4162 = FStar_ToSyntax_Env.qualify env x in
                (uu____4162, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4157 in
            (env, uu____4156, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4182 =
                  let uu____4183 =
                    let uu____4188 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4188, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4183 in
                mklet uu____4182
            | FStar_Parser_AST.PatVar (x,uu____4190) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4196);
                   FStar_Parser_AST.prange = uu____4197;_},t)
                ->
                let uu____4203 =
                  let uu____4204 =
                    let uu____4209 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4210 = desugar_term env t in
                    (uu____4209, uu____4210) in
                  LetBinder uu____4204 in
                (env, uu____4203, [])
            | uu____4213 ->
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4223 = desugar_data_pat env p is_mut in
             match uu____4223 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4252;
                       FStar_Syntax_Syntax.p = uu____4253;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4258;
                       FStar_Syntax_Syntax.p = uu____4259;_}::[] -> []
                   | uu____4264 -> p1 in
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
  fun uu____4271  ->
    fun env  ->
      fun pat  ->
        let uu____4274 = desugar_data_pat env pat false in
        match uu____4274 with | (env1,uu____4290,pat1) -> (env1, pat1)
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
      fun uu____4308  ->
        fun range  ->
          match uu____4308 with
          | (signedness,width) ->
              let uu____4316 = FStar_Const.bounds signedness width in
              (match uu____4316 with
               | (lower,upper) ->
                   let value =
                     let uu____4324 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4324 in
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
                      (let uu____4327 =
                         let uu____4328 =
                           let uu____4333 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____4333, range) in
                         FStar_Errors.Error uu____4328 in
                       FStar_Exn.raise uu____4327)
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
                       let uu____4341 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4341 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4351)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____4361 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____4361 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___240_4362 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___240_4362.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___240_4362.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4363 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4370 =
                             let uu____4371 =
                               let uu____4376 =
                                 FStar_Util.format1
                                   "Unexpected numeric literal.  Restart F* to load %s."
                                   tnm in
                               (uu____4376, range) in
                             FStar_Errors.Error uu____4371 in
                           FStar_Exn.raise uu____4370 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____4392 =
                       let uu____4395 =
                         let uu____4396 =
                           let uu____4411 =
                             let uu____4420 =
                               let uu____4427 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4427) in
                             [uu____4420] in
                           (lid1, uu____4411) in
                         FStar_Syntax_Syntax.Tm_app uu____4396 in
                       FStar_Syntax_Syntax.mk uu____4395 in
                     uu____4392 FStar_Pervasives_Native.None range)))
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
            let uu____4466 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4466 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4481 =
                    let uu____4482 =
                      let uu____4489 = mk_ref_read tm1 in
                      (uu____4489,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4482 in
                  FStar_All.pipe_left mk1 uu____4481
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4505 =
          let uu____4506 = unparen t in uu____4506.FStar_Parser_AST.tm in
        match uu____4505 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4507; FStar_Ident.ident = uu____4508;
              FStar_Ident.nsstr = uu____4509; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4512 ->
            let uu____4513 =
              let uu____4514 =
                let uu____4519 =
                  let uu____4520 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4520 in
                (uu____4519, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4514 in
            FStar_Exn.raise uu____4513 in
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
          let uu___241_4540 = e in
          {
            FStar_Syntax_Syntax.n = (uu___241_4540.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___241_4540.FStar_Syntax_Syntax.vars)
          } in
        let uu____4543 =
          let uu____4544 = unparen top in uu____4544.FStar_Parser_AST.tm in
        match uu____4543 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4545 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4596::uu____4597::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4601 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4601 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4614;_},t1::t2::[])
                  ->
                  let uu____4619 = flatten1 t1 in
                  FStar_List.append uu____4619 [t2]
              | uu____4622 -> [t] in
            let targs =
              let uu____4626 =
                let uu____4629 = unparen top in flatten1 uu____4629 in
              FStar_All.pipe_right uu____4626
                (FStar_List.map
                   (fun t  ->
                      let uu____4637 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4637)) in
            let uu____4638 =
              let uu____4643 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4643 in
            (match uu____4638 with
             | (tup,uu____4649) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4653 =
              let uu____4656 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4656 in
            FStar_All.pipe_left setpos uu____4653
        | FStar_Parser_AST.Uvar u ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4676 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____4676 with
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
                             let uu____4708 = desugar_term env t in
                             (uu____4708, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4722)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4737 =
              let uu___242_4738 = top in
              let uu____4739 =
                let uu____4740 =
                  let uu____4747 =
                    let uu___243_4748 = top in
                    let uu____4749 =
                      let uu____4750 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4750 in
                    {
                      FStar_Parser_AST.tm = uu____4749;
                      FStar_Parser_AST.range =
                        (uu___243_4748.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___243_4748.FStar_Parser_AST.level)
                    } in
                  (uu____4747, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4740 in
              {
                FStar_Parser_AST.tm = uu____4739;
                FStar_Parser_AST.range =
                  (uu___242_4738.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___242_4738.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4737
        | FStar_Parser_AST.Construct (n1,(a,uu____4753)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____4768 =
              let uu___244_4769 = top in
              let uu____4770 =
                let uu____4771 =
                  let uu____4778 =
                    let uu___245_4779 = top in
                    let uu____4780 =
                      let uu____4781 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4781 in
                    {
                      FStar_Parser_AST.tm = uu____4780;
                      FStar_Parser_AST.range =
                        (uu___245_4779.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___245_4779.FStar_Parser_AST.level)
                    } in
                  (uu____4778, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4771 in
              {
                FStar_Parser_AST.tm = uu____4770;
                FStar_Parser_AST.range =
                  (uu___244_4769.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___244_4769.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4768
        | FStar_Parser_AST.Construct (n1,(a,uu____4784)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4799 =
              let uu___246_4800 = top in
              let uu____4801 =
                let uu____4802 =
                  let uu____4809 =
                    let uu___247_4810 = top in
                    let uu____4811 =
                      let uu____4812 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4812 in
                    {
                      FStar_Parser_AST.tm = uu____4811;
                      FStar_Parser_AST.range =
                        (uu___247_4810.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___247_4810.FStar_Parser_AST.level)
                    } in
                  (uu____4809, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4802 in
              {
                FStar_Parser_AST.tm = uu____4801;
                FStar_Parser_AST.range =
                  (uu___246_4800.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___246_4800.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4799
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4813; FStar_Ident.ident = uu____4814;
              FStar_Ident.nsstr = uu____4815; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4818; FStar_Ident.ident = uu____4819;
              FStar_Ident.nsstr = uu____4820; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4823; FStar_Ident.ident = uu____4824;
               FStar_Ident.nsstr = uu____4825; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4843 =
              let uu____4844 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4844 in
            mk1 uu____4843
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4845; FStar_Ident.ident = uu____4846;
              FStar_Ident.nsstr = uu____4847; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4850; FStar_Ident.ident = uu____4851;
              FStar_Ident.nsstr = uu____4852; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4855; FStar_Ident.ident = uu____4856;
              FStar_Ident.nsstr = uu____4857; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4862;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____4864 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4864 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4869 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4869))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4873 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4873 with
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
                let uu____4900 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____4900 with
                | FStar_Pervasives_Native.Some uu____4909 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____4914 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____4914 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____4928 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____4941 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____4941
              | uu____4942 ->
                  let uu____4949 =
                    let uu____4950 =
                      let uu____4955 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____4955, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____4950 in
                  FStar_Exn.raise uu____4949))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____4958 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____4958 with
              | FStar_Pervasives_Native.None  ->
                  let uu____4961 =
                    let uu____4962 =
                      let uu____4967 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____4967, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____4962 in
                  FStar_Exn.raise uu____4961
              | uu____4968 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____4987 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____4987 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____4991 =
                    let uu____4998 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____4998, true) in
                  (match uu____4991 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5013 ->
                            let uu____5020 =
                              FStar_Util.take
                                (fun uu____5044  ->
                                   match uu____5044 with
                                   | (uu____5049,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5020 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5113  ->
                                        match uu____5113 with
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
                    let uu____5156 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5156 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5159 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5166 =
              FStar_List.fold_left
                (fun uu____5211  ->
                   fun b  ->
                     match uu____5211 with
                     | (env1,tparams,typs) ->
                         let uu____5268 = desugar_binder env1 b in
                         (match uu____5268 with
                          | (xopt,t1) ->
                              let uu____5297 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5306 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5306)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5297 with
                               | (env2,x) ->
                                   let uu____5326 =
                                     let uu____5329 =
                                       let uu____5332 =
                                         let uu____5333 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5333 in
                                       [uu____5332] in
                                     FStar_List.append typs uu____5329 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___248_5359 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___248_5359.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___248_5359.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5326)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5166 with
             | (env1,uu____5383,targs) ->
                 let uu____5405 =
                   let uu____5410 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5410 in
                 (match uu____5405 with
                  | (tup,uu____5416) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5427 = uncurry binders t in
            (match uu____5427 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___219_5459 =
                   match uu___219_5459 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5473 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5473
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5495 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5495 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5510 = desugar_binder env b in
            (match uu____5510 with
             | (FStar_Pervasives_Native.None ,uu____5517) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5527 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5527 with
                  | ((x,uu____5533),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5540 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5540))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5560 =
              FStar_List.fold_left
                (fun uu____5580  ->
                   fun pat  ->
                     match uu____5580 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5606,t) ->
                              let uu____5608 =
                                let uu____5611 = free_type_vars env1 t in
                                FStar_List.append uu____5611 ftvs in
                              (env1, uu____5608)
                          | uu____5616 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5560 with
             | (uu____5621,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5633 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5633 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___220_5674 =
                   match uu___220_5674 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5712 =
                                 let uu____5713 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5713
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5712 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5766 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5766
                   | p::rest ->
                       let uu____5777 = desugar_binding_pat env1 p in
                       (match uu____5777 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5801 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5806 =
                              match b with
                              | LetBinder uu____5839 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____5889) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____5925 =
                                          let uu____5930 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____5930, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____5925
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____5966,uu____5967) ->
                                             let tup2 =
                                               let uu____5969 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____5969
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____5973 =
                                                 let uu____5976 =
                                                   let uu____5977 =
                                                     let uu____5992 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____5995 =
                                                       let uu____5998 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____5999 =
                                                         let uu____6002 =
                                                           let uu____6003 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6003 in
                                                         [uu____6002] in
                                                       uu____5998 ::
                                                         uu____5999 in
                                                     (uu____5992, uu____5995) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____5977 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____5976 in
                                               uu____5973
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6014 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6014 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6045,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6047,pats)) ->
                                             let tupn =
                                               let uu____6086 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6086
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6096 =
                                                 let uu____6097 =
                                                   let uu____6112 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6115 =
                                                     let uu____6124 =
                                                       let uu____6133 =
                                                         let uu____6134 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6134 in
                                                       [uu____6133] in
                                                     FStar_List.append args
                                                       uu____6124 in
                                                   (uu____6112, uu____6115) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6097 in
                                               mk1 uu____6096 in
                                             let p2 =
                                               let uu____6154 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6154 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6189 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5806 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6256,uu____6257,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6271 =
                let uu____6272 = unparen e in uu____6272.FStar_Parser_AST.tm in
              match uu____6271 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6278 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6282 ->
            let rec aux args e =
              let uu____6314 =
                let uu____6315 = unparen e in uu____6315.FStar_Parser_AST.tm in
              match uu____6314 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6328 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6328 in
                  aux (arg :: args) e1
              | uu____6341 ->
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
              let uu____6367 =
                let uu____6368 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6368 in
              FStar_Parser_AST.mk_term uu____6367 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6369 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6369
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6372 =
              let uu____6373 =
                let uu____6380 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6380,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6373 in
            mk1 uu____6372
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6398 =
              let uu____6403 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6403 then desugar_typ else desugar_term in
            uu____6398 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6436 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6522  ->
                        match uu____6522 with
                        | (p,def) ->
                            let uu____6547 = is_app_pattern p in
                            if uu____6547
                            then
                              let uu____6566 =
                                destruct_app_pattern env top_level p in
                              (uu____6566, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6620 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6620, def1)
                               | uu____6649 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6675);
                                           FStar_Parser_AST.prange =
                                             uu____6676;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6700 =
                                            let uu____6715 =
                                              let uu____6720 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6720 in
                                            (uu____6715, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6700, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6767)
                                        ->
                                        if top_level
                                        then
                                          let uu____6790 =
                                            let uu____6805 =
                                              let uu____6810 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6810 in
                                            (uu____6805, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6790, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6856 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6875 =
                FStar_List.fold_left
                  (fun uu____6935  ->
                     fun uu____6936  ->
                       match (uu____6935, uu____6936) with
                       | ((env1,fnames,rec_bindings),((f,uu____7019,uu____7020),uu____7021))
                           ->
                           let uu____7100 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7126 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7126 with
                                  | (env2,xx) ->
                                      let uu____7145 =
                                        let uu____7148 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7148 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7145))
                             | FStar_Util.Inr l ->
                                 let uu____7156 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7156, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7100 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6875 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7282 =
                    match uu____7282 with
                    | ((uu____7305,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7349 = is_comp_type env1 t in
                                if uu____7349
                                then
                                  ((let uu____7351 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7361 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7361)) in
                                    match uu____7351 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7364 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7366 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7366))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7364
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7370 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7370 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7374 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7389 =
                                let uu____7390 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7390
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7389 in
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
                  let uu____7424 =
                    let uu____7425 =
                      let uu____7438 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7438) in
                    FStar_Syntax_Syntax.Tm_let uu____7425 in
                  FStar_All.pipe_left mk1 uu____7424 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7469 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7469 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7496 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7496
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
                    | LocalBinder (x,uu____7508) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7511;
                              FStar_Syntax_Syntax.p = uu____7512;_}::[] ->
                              body1
                          | uu____7517 ->
                              let uu____7520 =
                                let uu____7523 =
                                  let uu____7524 =
                                    let uu____7547 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7548 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7547, uu____7548) in
                                  FStar_Syntax_Syntax.Tm_match uu____7524 in
                                FStar_Syntax_Syntax.mk uu____7523 in
                              uu____7520 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7558 =
                          let uu____7559 =
                            let uu____7572 =
                              let uu____7573 =
                                let uu____7574 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7574] in
                              FStar_Syntax_Subst.close uu____7573 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7572) in
                          FStar_Syntax_Syntax.Tm_let uu____7559 in
                        FStar_All.pipe_left mk1 uu____7558 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____7600 = is_rec || (is_app_pattern pat) in
            if uu____7600
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____7609 =
                let uu____7610 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7610 in
              mk1 uu____7609 in
            let uu____7611 =
              let uu____7612 =
                let uu____7635 =
                  let uu____7638 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7638
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7659 =
                  let uu____7674 =
                    let uu____7687 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7690 = desugar_term env t2 in
                    (uu____7687, FStar_Pervasives_Native.None, uu____7690) in
                  let uu____7699 =
                    let uu____7714 =
                      let uu____7727 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7730 = desugar_term env t3 in
                      (uu____7727, FStar_Pervasives_Native.None, uu____7730) in
                    [uu____7714] in
                  uu____7674 :: uu____7699 in
                (uu____7635, uu____7659) in
              FStar_Syntax_Syntax.Tm_match uu____7612 in
            mk1 uu____7611
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
            let desugar_branch uu____7871 =
              match uu____7871 with
              | (pat,wopt,b) ->
                  let uu____7889 = desugar_match_pat env pat in
                  (match uu____7889 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____7910 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____7910 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____7912 =
              let uu____7913 =
                let uu____7936 = desugar_term env e in
                let uu____7937 = FStar_List.collect desugar_branch branches in
                (uu____7936, uu____7937) in
              FStar_Syntax_Syntax.Tm_match uu____7913 in
            FStar_All.pipe_left mk1 uu____7912
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____7966 = is_comp_type env t in
              if uu____7966
              then
                let uu____7973 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____7973
              else
                (let uu____7979 = desugar_term env t in
                 FStar_Util.Inl uu____7979) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____7985 =
              let uu____7986 =
                let uu____8013 = desugar_term env e in
                (uu____8013, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____7986 in
            FStar_All.pipe_left mk1 uu____7985
        | FStar_Parser_AST.Record (uu____8038,[]) ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8075 = FStar_List.hd fields in
              match uu____8075 with | (f,uu____8087) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8129  ->
                        match uu____8129 with
                        | (g,uu____8135) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8141,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8155 =
                         let uu____8156 =
                           let uu____8161 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8161, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8156 in
                       FStar_Exn.raise uu____8155
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
                  let uu____8169 =
                    let uu____8180 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8211  ->
                              match uu____8211 with
                              | (f,uu____8221) ->
                                  let uu____8222 =
                                    let uu____8223 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8223 in
                                  (uu____8222, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8180) in
                  FStar_Parser_AST.Construct uu____8169
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8241 =
                      let uu____8242 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8242 in
                    FStar_Parser_AST.mk_term uu____8241 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8244 =
                      let uu____8257 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8287  ->
                                match uu____8287 with
                                | (f,uu____8297) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8257) in
                    FStar_Parser_AST.Record uu____8244 in
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
                         FStar_Syntax_Syntax.pos = uu____8325;
                         FStar_Syntax_Syntax.vars = uu____8326;_},args);
                    FStar_Syntax_Syntax.pos = uu____8328;
                    FStar_Syntax_Syntax.vars = uu____8329;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8357 =
                     let uu____8358 =
                       let uu____8373 =
                         let uu____8374 =
                           let uu____8377 =
                             let uu____8378 =
                               let uu____8385 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8385) in
                             FStar_Syntax_Syntax.Record_ctor uu____8378 in
                           FStar_Pervasives_Native.Some uu____8377 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8374 in
                       (uu____8373, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8358 in
                   FStar_All.pipe_left mk1 uu____8357 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8416 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8420 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8420 with
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
                  let uu____8439 =
                    let uu____8440 =
                      let uu____8455 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8456 =
                        let uu____8459 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8459] in
                      (uu____8455, uu____8456) in
                    FStar_Syntax_Syntax.Tm_app uu____8440 in
                  FStar_All.pipe_left mk1 uu____8439))
        | FStar_Parser_AST.NamedTyp (uu____8464,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8467 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8468 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8469,uu____8470,uu____8471) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8484,uu____8485,uu____8486) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8499,uu____8500,uu____8501) ->
            failwith "Not implemented yet"
and not_ascribed: FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8515 -> false
    | uu____8524 -> true
and is_synth_by_tactic:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8530 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8530 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8534 -> false
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
           (fun uu____8571  ->
              match uu____8571 with
              | (a,imp) ->
                  let uu____8584 = desugar_term env a in
                  arg_withimp_e imp uu____8584))
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
        let is_requires uu____8603 =
          match uu____8603 with
          | (t1,uu____8609) ->
              let uu____8610 =
                let uu____8611 = unparen t1 in uu____8611.FStar_Parser_AST.tm in
              (match uu____8610 with
               | FStar_Parser_AST.Requires uu____8612 -> true
               | uu____8619 -> false) in
        let is_ensures uu____8627 =
          match uu____8627 with
          | (t1,uu____8633) ->
              let uu____8634 =
                let uu____8635 = unparen t1 in uu____8635.FStar_Parser_AST.tm in
              (match uu____8634 with
               | FStar_Parser_AST.Ensures uu____8636 -> true
               | uu____8643 -> false) in
        let is_app head1 uu____8654 =
          match uu____8654 with
          | (t1,uu____8660) ->
              let uu____8661 =
                let uu____8662 = unparen t1 in uu____8662.FStar_Parser_AST.tm in
              (match uu____8661 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8664;
                      FStar_Parser_AST.level = uu____8665;_},uu____8666,uu____8667)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____8668 -> false) in
        let is_smt_pat uu____8676 =
          match uu____8676 with
          | (t1,uu____8682) ->
              let uu____8683 =
                let uu____8684 = unparen t1 in uu____8684.FStar_Parser_AST.tm in
              (match uu____8683 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8687);
                             FStar_Parser_AST.range = uu____8688;
                             FStar_Parser_AST.level = uu____8689;_},uu____8690)::uu____8691::[])
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
                             FStar_Parser_AST.range = uu____8730;
                             FStar_Parser_AST.level = uu____8731;_},uu____8732)::uu____8733::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____8758 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8786 = head_and_args t1 in
          match uu____8786 with
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
                   let ens_true =
                     let ens =
                       FStar_Parser_AST.Ensures
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None) in
                     ((FStar_Parser_AST.mk_term ens t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let fail_lemma uu____8879 =
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
                     | ens::[] -> [unit_tm; req_true; ens; nil_pat]
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         [unit_tm; req; ens; nil_pat]
                     | ens::smtpat::[] when
                         (((let uu____9045 = is_requires ens in
                            Prims.op_Negation uu____9045) &&
                             (let uu____9047 = is_smt_pat ens in
                              Prims.op_Negation uu____9047))
                            &&
                            (let uu____9049 = is_decreases ens in
                             Prims.op_Negation uu____9049))
                           && (is_smt_pat smtpat)
                         -> [unit_tm; req_true; ens; smtpat]
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         [unit_tm; req_true; ens; nil_pat; dec]
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         -> [unit_tm; req_true; ens; smtpat; dec]
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         -> [unit_tm; req; ens; nil_pat; dec]
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         -> unit_tm :: args
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         -> unit_tm :: args
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9338 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9338, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9366 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9366
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9384 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9384
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
               | uu____9422 ->
                   let default_effect =
                     let uu____9424 = FStar_Options.ml_ish () in
                     if uu____9424
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9427 =
                           FStar_Options.warn_default_effects () in
                         if uu____9427
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9451 = pre_process_comp_typ t in
        match uu____9451 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9500 =
                  let uu____9501 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9501 in
                fail uu____9500)
             else ();
             (let is_universe uu____9510 =
                match uu____9510 with
                | (uu____9515,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9517 = FStar_Util.take is_universe args in
              match uu____9517 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9576  ->
                         match uu____9576 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9583 =
                    let uu____9598 = FStar_List.hd args1 in
                    let uu____9607 = FStar_List.tl args1 in
                    (uu____9598, uu____9607) in
                  (match uu____9583 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9662 =
                         let is_decrease uu____9698 =
                           match uu____9698 with
                           | (t1,uu____9708) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____9718;
                                       FStar_Syntax_Syntax.vars = uu____9719;_},uu____9720::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____9751 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9662 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____9865  ->
                                      match uu____9865 with
                                      | (t1,uu____9875) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____9884,(arg,uu____9886)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____9915 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____9929 -> false in
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
                                           | uu____10077 -> pat in
                                         let uu____10078 =
                                           let uu____10089 =
                                             let uu____10100 =
                                               let uu____10109 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10109, aq) in
                                             [uu____10100] in
                                           ens :: uu____10089 in
                                         req :: uu____10078
                                     | uu____10150 -> rest2
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
        | uu____10172 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___249_10189 = t in
        {
          FStar_Syntax_Syntax.n = (uu___249_10189.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___249_10189.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___250_10223 = b in
             {
               FStar_Parser_AST.b = (uu___250_10223.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___250_10223.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___250_10223.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10282 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10282)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10295 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10295 with
             | (env1,a1) ->
                 let a2 =
                   let uu___251_10305 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___251_10305.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___251_10305.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10327 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10341 =
                     let uu____10344 =
                       let uu____10345 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10345] in
                     no_annot_abs uu____10344 body2 in
                   FStar_All.pipe_left setpos uu____10341 in
                 let uu____10350 =
                   let uu____10351 =
                     let uu____10366 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10367 =
                       let uu____10370 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10370] in
                     (uu____10366, uu____10367) in
                   FStar_Syntax_Syntax.Tm_app uu____10351 in
                 FStar_All.pipe_left mk1 uu____10350)
        | uu____10375 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____10447 = q (rest, pats, body) in
              let uu____10454 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10447 uu____10454
                FStar_Parser_AST.Formula in
            let uu____10455 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10455 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10464 -> failwith "impossible" in
      let uu____10467 =
        let uu____10468 = unparen f in uu____10468.FStar_Parser_AST.tm in
      match uu____10467 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10475,uu____10476) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10487,uu____10488) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10519 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10519
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10555 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10555
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____10598 -> desugar_term env f
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
      let uu____10603 =
        FStar_List.fold_left
          (fun uu____10639  ->
             fun b  ->
               match uu____10639 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___252_10691 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___252_10691.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___252_10691.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___252_10691.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____10708 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____10708 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___253_10728 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___253_10728.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___253_10728.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____10745 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10603 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____10832 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____10832)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____10837 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____10837)
      | FStar_Parser_AST.TVariable x ->
          let uu____10841 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____10841)
      | FStar_Parser_AST.NoName t ->
          let uu____10849 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____10849)
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
               (fun uu___221_10885  ->
                  match uu___221_10885 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____10886 -> false)) in
        let quals2 q =
          let uu____10897 =
            (let uu____10900 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____10900) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____10897
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____10913 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____10913;
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
            let uu____10949 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____10979  ->
                        match uu____10979 with
                        | (x,uu____10987) ->
                            let uu____10988 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____10988 with
                             | (field_name,uu____10996) ->
                                 let only_decl =
                                   ((let uu____11000 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11000)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11002 =
                                        let uu____11003 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11003.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11002) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11017 =
                                       FStar_List.filter
                                         (fun uu___222_11021  ->
                                            match uu___222_11021 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11022 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11017
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___223_11035  ->
                                             match uu___223_11035 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11036 -> false)) in
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
                                      let uu____11044 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11044
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11049 =
                                        let uu____11054 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11054 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11049;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11056 =
                                        let uu____11057 =
                                          let uu____11064 =
                                            let uu____11067 =
                                              let uu____11068 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11068
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11067] in
                                          ((false, [lb]), uu____11064) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11057 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11056;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____10949 FStar_List.flatten
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
            (lid,uu____11115,t,uu____11117,n1,uu____11119) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11124 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11124 with
             | (formals,uu____11140) ->
                 (match formals with
                  | [] -> []
                  | uu____11163 ->
                      let filter_records uu___224_11175 =
                        match uu___224_11175 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11178,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11190 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11192 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11192 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11202 = FStar_Util.first_N n1 formals in
                      (match uu____11202 with
                       | (uu____11225,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11251 -> []
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
                    let uu____11309 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11309
                    then
                      let uu____11312 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11312
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11315 =
                      let uu____11320 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11320 in
                    let uu____11321 =
                      let uu____11324 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11324 in
                    let uu____11327 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11315;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11321;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11327
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
          let tycon_id uu___225_11376 =
            match uu___225_11376 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11378,uu____11379) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11389,uu____11390,uu____11391) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11401,uu____11402,uu____11403) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____11433,uu____11434,uu____11435) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11477) ->
                let uu____11478 =
                  let uu____11479 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11479 in
                FStar_Parser_AST.mk_term uu____11478 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11481 =
                  let uu____11482 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11482 in
                FStar_Parser_AST.mk_term uu____11481 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11484) ->
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
              | uu____11507 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11513 =
                     let uu____11514 =
                       let uu____11521 = binder_to_term b in
                       (out, uu____11521, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11514 in
                   FStar_Parser_AST.mk_term uu____11513
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___226_11531 =
            match uu___226_11531 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____11586  ->
                       match uu____11586 with
                       | (x,t,uu____11597) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____11603 =
                    let uu____11604 =
                      let uu____11605 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11605 in
                    FStar_Parser_AST.mk_term uu____11604
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11603 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11609 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11636  ->
                          match uu____11636 with
                          | (x,uu____11646,uu____11647) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____11609)
            | uu____11700 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___227_11731 =
            match uu___227_11731 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____11755 = typars_of_binders _env binders in
                (match uu____11755 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____11801 =
                         let uu____11802 =
                           let uu____11803 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____11803 in
                         FStar_Parser_AST.mk_term uu____11802
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____11801 binders in
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
            | uu____11816 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____11860 =
              FStar_List.fold_left
                (fun uu____11900  ->
                   fun uu____11901  ->
                     match (uu____11900, uu____11901) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____11992 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____11992 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____11860 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12105 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12105
                | uu____12106 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12114 = desugar_abstract_tc quals env [] tc in
              (match uu____12114 with
               | (uu____12127,uu____12128,se,uu____12130) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12133,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12150 =
                                 let uu____12151 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12151 in
                               if uu____12150
                               then
                                 let uu____12152 =
                                   let uu____12153 =
                                     FStar_Syntax_Print.lid_to_string l in
                                   FStar_Util.format1
                                     "Adding an implicit 'assume new' qualifier on %s"
                                     uu____12153 in
                                 FStar_Errors.warn
                                   se.FStar_Syntax_Syntax.sigrng uu____12152
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12160 ->
                               let uu____12161 =
                                 let uu____12164 =
                                   let uu____12165 =
                                     let uu____12178 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12178) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12165 in
                                 FStar_Syntax_Syntax.mk uu____12164 in
                               uu____12161 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___254_12182 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___254_12182.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___254_12182.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___254_12182.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12185 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12188 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12188
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12203 = typars_of_binders env binders in
              (match uu____12203 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12239 =
                           FStar_Util.for_some
                             (fun uu___228_12241  ->
                                match uu___228_12241 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12242 -> false) quals in
                         if uu____12239
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12249 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___229_12253  ->
                               match uu___229_12253 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12254 -> false)) in
                     if uu____12249
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12263 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12263
                     then
                       let uu____12266 =
                         let uu____12273 =
                           let uu____12274 = unparen t in
                           uu____12274.FStar_Parser_AST.tm in
                         match uu____12273 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12295 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12325)::args_rev ->
                                   let uu____12337 =
                                     let uu____12338 = unparen last_arg in
                                     uu____12338.FStar_Parser_AST.tm in
                                   (match uu____12337 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12366 -> ([], args))
                               | uu____12375 -> ([], args) in
                             (match uu____12295 with
                              | (cattributes,args1) ->
                                  let uu____12414 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12414))
                         | uu____12425 -> (t, []) in
                       match uu____12266 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___230_12447  ->
                                     match uu___230_12447 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____12448 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____12459)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12483 = tycon_record_as_variant trec in
              (match uu____12483 with
               | (t,fs) ->
                   let uu____12500 =
                     let uu____12503 =
                       let uu____12504 =
                         let uu____12513 =
                           let uu____12516 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12516 in
                         (uu____12513, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12504 in
                     uu____12503 :: quals in
                   desugar_tycon env d uu____12500 [t])
          | uu____12521::uu____12522 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____12683 = et in
                match uu____12683 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____12908 ->
                         let trec = tc in
                         let uu____12932 = tycon_record_as_variant trec in
                         (match uu____12932 with
                          | (t,fs) ->
                              let uu____12991 =
                                let uu____12994 =
                                  let uu____12995 =
                                    let uu____13004 =
                                      let uu____13007 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13007 in
                                    (uu____13004, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____12995 in
                                uu____12994 :: quals1 in
                              collect_tcs uu____12991 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13094 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13094 with
                          | (env2,uu____13154,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13303 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13303 with
                          | (env2,uu____13363,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13488 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13535 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13535 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___232_14046  ->
                             match uu___232_14046 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14113,uu____14114);
                                    FStar_Syntax_Syntax.sigrng = uu____14115;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14116;
                                    FStar_Syntax_Syntax.sigmeta = uu____14117;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14118;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14179 =
                                     typars_of_binders env1 binders in
                                   match uu____14179 with
                                   | (env2,tpars1) ->
                                       let uu____14210 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14210 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14243 =
                                   let uu____14264 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14264) in
                                 [uu____14243]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14332);
                                    FStar_Syntax_Syntax.sigrng = uu____14333;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14335;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14336;_},constrs,tconstr,quals1)
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
                                 let uu____14432 = push_tparams env1 tpars in
                                 (match uu____14432 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14509  ->
                                             match uu____14509 with
                                             | (x,uu____14523) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14531 =
                                        let uu____14560 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____14674  ->
                                                  match uu____14674 with
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
                                                        let uu____14730 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____14730 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___231_14741
                                                                 ->
                                                                match uu___231_14741
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____14753
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____14761 =
                                                        let uu____14782 =
                                                          let uu____14783 =
                                                            let uu____14784 =
                                                              let uu____14799
                                                                =
                                                                let uu____14802
                                                                  =
                                                                  let uu____14805
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____14805 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____14802 in
                                                              (name, univs1,
                                                                uu____14799,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____14784 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____14783;
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
                                                          uu____14782) in
                                                      (name, uu____14761))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14560 in
                                      (match uu____14531 with
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
                             | uu____15044 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15176  ->
                             match uu____15176 with
                             | (name_doc,uu____15204,uu____15205) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15285  ->
                             match uu____15285 with
                             | (uu____15306,uu____15307,se) -> se)) in
                   let uu____15337 =
                     let uu____15344 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15344 rng in
                   (match uu____15337 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____15410  ->
                                  match uu____15410 with
                                  | (uu____15433,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15484,tps,k,uu____15487,constrs)
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
                                  | uu____15506 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15523  ->
                                 match uu____15523 with
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
      let uu____15560 =
        FStar_List.fold_left
          (fun uu____15583  ->
             fun b  ->
               match uu____15583 with
               | (env1,binders1) ->
                   let uu____15603 = desugar_binder env1 b in
                   (match uu____15603 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15620 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15620 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15637 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____15560 with
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
                let uu____15755 = desugar_binders monad_env eff_binders in
                match uu____15755 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____15776 =
                        let uu____15777 =
                          let uu____15784 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____15784 in
                        FStar_List.length uu____15777 in
                      uu____15776 = (Prims.parse_int "1") in
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
                          (uu____15826,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____15828,uu____15829,uu____15830),uu____15831)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____15864 ->
                          failwith "Malformed effect member declaration." in
                    let uu____15865 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____15877 = name_of_eff_decl decl in
                           FStar_List.mem uu____15877 mandatory_members)
                        eff_decls in
                    (match uu____15865 with
                     | (mandatory_members_decls,actions) ->
                         let uu____15894 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____15923  ->
                                   fun decl  ->
                                     match uu____15923 with
                                     | (env2,out) ->
                                         let uu____15943 =
                                           desugar_decl env2 decl in
                                         (match uu____15943 with
                                          | (env3,ses) ->
                                              let uu____15956 =
                                                let uu____15959 =
                                                  FStar_List.hd ses in
                                                uu____15959 :: out in
                                              (env3, uu____15956)))
                                (env1, [])) in
                         (match uu____15894 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16027,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16030,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16031,
                                                                (def,uu____16033)::
                                                                (cps_type,uu____16035)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16036;
                                                             FStar_Parser_AST.level
                                                               = uu____16037;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16089 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16089 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16109 =
                                                   let uu____16110 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16111 =
                                                     let uu____16112 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16112 in
                                                   let uu____16117 =
                                                     let uu____16118 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16118 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16110;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16111;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16117
                                                   } in
                                                 (uu____16109, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16125,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16128,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16163 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16163 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16183 =
                                                   let uu____16184 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16185 =
                                                     let uu____16186 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16186 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16184;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16185;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16183, doc1))
                                        | uu____16193 ->
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
                                let uu____16223 =
                                  let uu____16224 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16224 in
                                ([], uu____16223) in
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
                                    let uu____16241 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16241) in
                                  let uu____16248 =
                                    let uu____16249 =
                                      let uu____16250 =
                                        let uu____16251 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16251 in
                                      let uu____16260 = lookup "return" in
                                      let uu____16261 = lookup "bind" in
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
                                          uu____16250;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16260;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16261;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16249 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16248;
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
                                       (fun uu___233_16265  ->
                                          match uu___233_16265 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16266 -> true
                                          | uu____16267 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16277 =
                                     let uu____16278 =
                                       let uu____16279 = lookup "return_wp" in
                                       let uu____16280 = lookup "bind_wp" in
                                       let uu____16281 =
                                         lookup "if_then_else" in
                                       let uu____16282 = lookup "ite_wp" in
                                       let uu____16283 = lookup "stronger" in
                                       let uu____16284 = lookup "close_wp" in
                                       let uu____16285 = lookup "assert_p" in
                                       let uu____16286 = lookup "assume_p" in
                                       let uu____16287 = lookup "null_wp" in
                                       let uu____16288 = lookup "trivial" in
                                       let uu____16289 =
                                         if rr
                                         then
                                           let uu____16290 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16290
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16306 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16308 =
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
                                           uu____16279;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16280;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16281;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16282;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16283;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16284;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16285;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16286;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16287;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16288;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16289;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16306;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16308;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16278 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16277;
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
                                        fun uu____16333  ->
                                          match uu____16333 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16347 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16347 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16349 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16349
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
                let uu____16380 = desugar_binders env1 eff_binders in
                match uu____16380 with
                | (env2,binders) ->
                    let uu____16399 =
                      let uu____16418 = head_and_args defn in
                      match uu____16418 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16463 ->
                                let uu____16464 =
                                  let uu____16465 =
                                    let uu____16470 =
                                      let uu____16471 =
                                        let uu____16472 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____16472 " not found" in
                                      Prims.strcat "Effect " uu____16471 in
                                    (uu____16470,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16465 in
                                FStar_Exn.raise uu____16464 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16474 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16504)::args_rev ->
                                let uu____16516 =
                                  let uu____16517 = unparen last_arg in
                                  uu____16517.FStar_Parser_AST.tm in
                                (match uu____16516 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16545 -> ([], args))
                            | uu____16554 -> ([], args) in
                          (match uu____16474 with
                           | (cattributes,args1) ->
                               let uu____16605 = desugar_args env2 args1 in
                               let uu____16614 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16605, uu____16614)) in
                    (match uu____16399 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____16673 =
                           match uu____16673 with
                           | (uu____16686,x) ->
                               let uu____16692 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____16692 with
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
                                      let uu____16718 =
                                        let uu____16719 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____16719 in
                                      ([], uu____16718)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____16724 =
                             let uu____16725 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____16725 in
                           let uu____16736 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____16737 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____16738 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____16739 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____16740 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____16741 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____16742 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____16743 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____16744 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____16745 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____16746 =
                             let uu____16747 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____16747 in
                           let uu____16758 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____16759 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____16760 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____16768 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____16769 =
                                    let uu____16770 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____16770 in
                                  let uu____16781 =
                                    let uu____16782 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____16782 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____16768;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____16769;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____16781
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____16724;
                             FStar_Syntax_Syntax.ret_wp = uu____16736;
                             FStar_Syntax_Syntax.bind_wp = uu____16737;
                             FStar_Syntax_Syntax.if_then_else = uu____16738;
                             FStar_Syntax_Syntax.ite_wp = uu____16739;
                             FStar_Syntax_Syntax.stronger = uu____16740;
                             FStar_Syntax_Syntax.close_wp = uu____16741;
                             FStar_Syntax_Syntax.assert_p = uu____16742;
                             FStar_Syntax_Syntax.assume_p = uu____16743;
                             FStar_Syntax_Syntax.null_wp = uu____16744;
                             FStar_Syntax_Syntax.trivial = uu____16745;
                             FStar_Syntax_Syntax.repr = uu____16746;
                             FStar_Syntax_Syntax.return_repr = uu____16758;
                             FStar_Syntax_Syntax.bind_repr = uu____16759;
                             FStar_Syntax_Syntax.actions = uu____16760
                           } in
                         let se =
                           let for_free =
                             let uu____16795 =
                               let uu____16796 =
                                 let uu____16803 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____16803 in
                               FStar_List.length uu____16796 in
                             uu____16795 = (Prims.parse_int "1") in
                           let uu____16832 =
                             let uu____16835 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____16835 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____16832;
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
                                       let uu____16855 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____16855 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____16857 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____16857
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
    let uu____16872 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____16872 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____16923 ->
              let uu____16924 =
                let uu____16925 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____16925 in
              Prims.strcat "\n  " uu____16924
          | uu____16926 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____16939  ->
               match uu____16939 with
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
          let uu____16957 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____16957
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____16959 =
          let uu____16968 = FStar_Syntax_Syntax.as_arg arg in [uu____16968] in
        FStar_Syntax_Util.mk_app fv uu____16959
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____16975 = desugar_decl_noattrs env d in
      match uu____16975 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____16995 = mk_comment_attr d in uu____16995 :: attrs1 in
          let uu____17000 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___255_17006 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___255_17006.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___255_17006.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___255_17006.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___255_17006.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____17000)
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
      | FStar_Parser_AST.Fsdoc uu____17032 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17048 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17048, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17087  ->
                 match uu____17087 with | (x,uu____17095) -> x) tcs in
          let uu____17100 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17100 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17122;
                    FStar_Parser_AST.prange = uu____17123;_},uu____17124)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17133;
                    FStar_Parser_AST.prange = uu____17134;_},uu____17135)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17150;
                         FStar_Parser_AST.prange = uu____17151;_},uu____17152);
                    FStar_Parser_AST.prange = uu____17153;_},uu____17154)::[]
                   -> false
               | (p,uu____17170)::[] ->
                   let uu____17179 = is_app_pattern p in
                   Prims.op_Negation uu____17179
               | uu____17180 -> false) in
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
            let uu____17199 =
              let uu____17200 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17200.FStar_Syntax_Syntax.n in
            (match uu____17199 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17208) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17241::uu____17242 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17245 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___234_17258  ->
                               match uu___234_17258 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17261;
                                   FStar_Syntax_Syntax.lbunivs = uu____17262;
                                   FStar_Syntax_Syntax.lbtyp = uu____17263;
                                   FStar_Syntax_Syntax.lbeff = uu____17264;
                                   FStar_Syntax_Syntax.lbdef = uu____17265;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17273;
                                   FStar_Syntax_Syntax.lbtyp = uu____17274;
                                   FStar_Syntax_Syntax.lbeff = uu____17275;
                                   FStar_Syntax_Syntax.lbdef = uu____17276;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17286 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17300  ->
                             match uu____17300 with
                             | (uu____17305,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17286
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17317 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17317
                   then
                     let uu____17326 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___256_17340 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___257_17342 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___257_17342.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___257_17342.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___256_17340.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___256_17340.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___256_17340.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___256_17340.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17326)
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
             | uu____17374 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17380 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17399 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17380 with
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
                       let uu___258_17423 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___258_17423.FStar_Parser_AST.prange)
                       }
                   | uu____17424 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___259_17431 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___259_17431.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___259_17431.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___259_17431.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17463 id =
                   match uu____17463 with
                   | (env1,ses) ->
                       let main =
                         let uu____17484 =
                           let uu____17485 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17485 in
                         FStar_Parser_AST.mk_term uu____17484
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
                       let uu____17535 = desugar_decl env1 id_decl in
                       (match uu____17535 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17553 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17553 FStar_Util.set_elements in
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
            let uu____17584 = close_fun env t in desugar_term env uu____17584 in
          let quals1 =
            let uu____17588 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17588
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____17594 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17594;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17606 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____17606 with
           | (t,uu____17620) ->
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
            let uu____17654 =
              let uu____17661 = FStar_Syntax_Syntax.null_binder t in
              [uu____17661] in
            let uu____17662 =
              let uu____17665 =
                let uu____17666 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17666 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17665 in
            FStar_Syntax_Util.arrow uu____17654 uu____17662 in
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
            let uu____17728 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____17728 with
            | FStar_Pervasives_Native.None  ->
                let uu____17731 =
                  let uu____17732 =
                    let uu____17737 =
                      let uu____17738 =
                        let uu____17739 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____17739 " not found" in
                      Prims.strcat "Effect name " uu____17738 in
                    (uu____17737, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____17732 in
                FStar_Exn.raise uu____17731
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____17743 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____17785 =
                  let uu____17794 =
                    let uu____17801 = desugar_term env t in ([], uu____17801) in
                  FStar_Pervasives_Native.Some uu____17794 in
                (uu____17785, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____17834 =
                  let uu____17843 =
                    let uu____17850 = desugar_term env wp in
                    ([], uu____17850) in
                  FStar_Pervasives_Native.Some uu____17843 in
                let uu____17859 =
                  let uu____17868 =
                    let uu____17875 = desugar_term env t in ([], uu____17875) in
                  FStar_Pervasives_Native.Some uu____17868 in
                (uu____17834, uu____17859)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____17901 =
                  let uu____17910 =
                    let uu____17917 = desugar_term env t in ([], uu____17917) in
                  FStar_Pervasives_Native.Some uu____17910 in
                (FStar_Pervasives_Native.None, uu____17901) in
          (match uu____17743 with
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
      let uu____18007 =
        FStar_List.fold_left
          (fun uu____18027  ->
             fun d  ->
               match uu____18027 with
               | (env1,sigelts) ->
                   let uu____18047 = desugar_decl env1 d in
                   (match uu____18047 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____18007 with
      | (env1,sigelts) ->
          let rec forward acc uu___236_18088 =
            match uu___236_18088 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18102,FStar_Syntax_Syntax.Sig_let uu____18103) ->
                     let uu____18116 =
                       let uu____18119 =
                         let uu___260_18120 = se2 in
                         let uu____18121 =
                           let uu____18124 =
                             FStar_List.filter
                               (fun uu___235_18138  ->
                                  match uu___235_18138 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18142;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18143;_},uu____18144);
                                      FStar_Syntax_Syntax.pos = uu____18145;
                                      FStar_Syntax_Syntax.vars = uu____18146;_}
                                      when
                                      let uu____18169 =
                                        let uu____18170 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____18170 in
                                      uu____18169 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18171 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____18124
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___260_18120.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___260_18120.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___260_18120.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___260_18120.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18121
                         } in
                       uu____18119 :: se1 :: acc in
                     forward uu____18116 sigelts1
                 | uu____18176 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____18184 = forward [] sigelts in (env1, uu____18184)
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
          | (FStar_Pervasives_Native.None ,uu____18238) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18242;
               FStar_Syntax_Syntax.exports = uu____18243;
               FStar_Syntax_Syntax.is_interface = uu____18244;_},FStar_Parser_AST.Module
             (current_lid,uu____18246)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18254) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18257 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18293 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18293, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18310 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18310, mname, decls, false) in
        match uu____18257 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18340 = desugar_decls env2 decls in
            (match uu____18340 with
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
          let uu____18398 =
            (FStar_Options.interactive ()) &&
              (let uu____18400 =
                 let uu____18401 =
                   let uu____18402 = FStar_Options.file_list () in
                   FStar_List.hd uu____18402 in
                 FStar_Util.get_file_extension uu____18401 in
               FStar_List.mem uu____18400 ["fsti"; "fsi"]) in
          if uu____18398 then as_interface m else m in
        let uu____18406 = desugar_modul_common curmod env m1 in
        match uu____18406 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18421 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18439 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18439 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18455 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18455
            then
              let uu____18456 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18456
            else ());
           (let uu____18458 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18458, modul)))
let ast_modul_to_modul:
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____18473 = desugar_modul env modul in
      match uu____18473 with | (env1,modul1) -> (modul1, env1)
let decls_to_sigelts:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____18501 = desugar_decls env decls in
      match uu____18501 with | (env1,sigelts) -> (sigelts, env1)
let partial_ast_modul_to_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____18541 = desugar_partial_modul modul env a_modul in
        match uu____18541 with | (env1,modul1) -> (modul1, env1)
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun m  ->
    fun mii  ->
      fun en  ->
        let uu____18569 =
          FStar_ToSyntax_Env.prepare_module_or_interface false false en
            m.FStar_Syntax_Syntax.name mii in
        match uu____18569 with
        | (en1,pop_when_done) ->
            let en2 =
              let uu____18581 =
                FStar_ToSyntax_Env.set_current_module en1
                  m.FStar_Syntax_Syntax.name in
              FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18581
                m.FStar_Syntax_Syntax.exports in
            let env = FStar_ToSyntax_Env.finish en2 m in
            let uu____18583 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  m.FStar_Syntax_Syntax.name env
              else env in
            ((), uu____18583)