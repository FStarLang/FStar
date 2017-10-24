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
  fun uu___219_62  ->
    match uu___219_62 with
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
      fun uu___220_83  ->
        match uu___220_83 with
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
  fun uu___221_91  ->
    match uu___221_91 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___222_101  ->
    match uu___222_101 with
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
  fun uu___223_1455  ->
    match uu___223_1455 with
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
      fun uu___224_1490  ->
        match uu___224_1490 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1506 = FStar_Syntax_Syntax.null_binder k in
            (uu____1506, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1511 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1511 with
             | (env1,a1) ->
                 (((let uu___247_1531 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___247_1531.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___247_1531.FStar_Syntax_Syntax.index);
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
  fun uu___225_1834  ->
    match uu___225_1834 with
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
                  (fun uu___226_2042  ->
                     match uu___226_2042 with
                     | FStar_Util.Inr uu____2047 -> true
                     | uu____2048 -> false) univargs
              then
                let uu____2053 =
                  let uu____2054 =
                    FStar_List.map
                      (fun uu___227_2063  ->
                         match uu___227_2063 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2054 in
                FStar_Util.Inr uu____2053
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___228_2080  ->
                        match uu___228_2080 with
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
        let check_linear_pattern_variables p1 r =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2418 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2425 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2426 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2428,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2469  ->
                          match uu____2469 with
                          | (p3,uu____2479) ->
                              let uu____2480 =
                                let uu____2481 =
                                  let uu____2484 = pat_vars p3 in
                                  FStar_Util.set_intersect uu____2484 out in
                                FStar_Util.set_is_empty uu____2481 in
                              if uu____2480
                              then
                                let uu____2489 = pat_vars p3 in
                                FStar_Util.set_union out uu____2489
                              else
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Non-linear patterns are not permitted.",
                                       r))) FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2496) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2497) -> ()
         | (true ,uu____2504) ->
             FStar_Exn.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____2539 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2539 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2553 ->
               let uu____2556 = push_bv_maybe_mut e x in
               (match uu____2556 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           let orig = p1 in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2643 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2659 =
                 let uu____2660 =
                   let uu____2661 =
                     let uu____2668 =
                       let uu____2669 =
                         let uu____2674 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2674, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2669 in
                     (uu____2668, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2661 in
                 {
                   FStar_Parser_AST.pat = uu____2660;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2659
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2679 = aux loc env1 p2 in
               (match uu____2679 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___248_2733 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___249_2738 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___249_2738.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___249_2738.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___248_2733.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___250_2740 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___251_2745 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___251_2745.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___251_2745.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___250_2740.FStar_Syntax_Syntax.p)
                          }
                      | uu____2746 when top -> p4
                      | uu____2747 ->
                          FStar_Exn.raise
                            (FStar_Errors.Error
                               ("Type ascriptions within patterns are only allowed on variables",
                                 (orig.FStar_Parser_AST.prange))) in
                    let uu____2750 =
                      match binder with
                      | LetBinder uu____2763 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2777 = close_fun env1 t in
                            desugar_term env1 uu____2777 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2779 -> true)
                           then
                             (let uu____2780 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2781 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2782 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                uu____2780 uu____2781 uu____2782)
                           else ();
                           (let uu____2784 = annot_pat_var p3 t1 in
                            (uu____2784,
                              (LocalBinder
                                 ((let uu___252_2790 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___252_2790.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___252_2790.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq))))) in
                    (match uu____2750 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2812 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2812, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2823 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2823, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2844 = resolvex loc env1 x in
               (match uu____2844 with
                | (loc1,env2,xbv) ->
                    let uu____2866 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2866, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2887 = resolvex loc env1 x in
               (match uu____2887 with
                | (loc1,env2,xbv) ->
                    let uu____2909 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2909, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2921 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2921, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2945;_},args)
               ->
               let uu____2951 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2992  ->
                        match uu____2992 with
                        | (loc1,env2,args1) ->
                            let uu____3040 = aux loc1 env2 arg in
                            (match uu____3040 with
                             | (loc2,env3,uu____3069,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2951 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3139 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3139, false))
           | FStar_Parser_AST.PatApp uu____3156 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3178 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3211  ->
                        match uu____3211 with
                        | (loc1,env2,pats1) ->
                            let uu____3243 = aux loc1 env2 pat in
                            (match uu____3243 with
                             | (loc2,env3,uu____3268,pat1,uu____3270) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3178 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3313 =
                        let uu____3316 =
                          let uu____3321 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3321 in
                        let uu____3322 =
                          let uu____3323 =
                            let uu____3336 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3336, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3323 in
                        FStar_All.pipe_left uu____3316 uu____3322 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3368 =
                               let uu____3369 =
                                 let uu____3382 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3382, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3369 in
                             FStar_All.pipe_left (pos_r r) uu____3368) pats1
                        uu____3313 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3426 =
                 FStar_List.fold_left
                   (fun uu____3466  ->
                      fun p2  ->
                        match uu____3466 with
                        | (loc1,env2,pats) ->
                            let uu____3515 = aux loc1 env2 p2 in
                            (match uu____3515 with
                             | (loc2,env3,uu____3544,pat,uu____3546) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3426 with
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
                    let uu____3641 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3641 with
                     | (constr,uu____3663) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3666 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3668 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3668, false)))
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
                      (fun uu____3739  ->
                         match uu____3739 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3769  ->
                         match uu____3769 with
                         | (f,uu____3775) ->
                             let uu____3776 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3802  ->
                                       match uu____3802 with
                                       | (g,uu____3808) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3776 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3813,p2)
                                  -> p2))) in
               let app =
                 let uu____3820 =
                   let uu____3821 =
                     let uu____3828 =
                       let uu____3829 =
                         let uu____3830 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3830 in
                       FStar_Parser_AST.mk_pattern uu____3829
                         p1.FStar_Parser_AST.prange in
                     (uu____3828, args) in
                   FStar_Parser_AST.PatApp uu____3821 in
                 FStar_Parser_AST.mk_pattern uu____3820
                   p1.FStar_Parser_AST.prange in
               let uu____3833 = aux loc env1 app in
               (match uu____3833 with
                | (env2,e,b,p2,uu____3862) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3890 =
                            let uu____3891 =
                              let uu____3904 =
                                let uu___253_3905 = fv in
                                let uu____3906 =
                                  let uu____3909 =
                                    let uu____3910 =
                                      let uu____3917 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3917) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3910 in
                                  FStar_Pervasives_Native.Some uu____3909 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___253_3905.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___253_3905.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3906
                                } in
                              (uu____3904, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3891 in
                          FStar_All.pipe_left pos uu____3890
                      | uu____3944 -> p2 in
                    (env2, e, b, p3, false))
         and aux loc env1 p1 = aux' false loc env1 p1 in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3994 = aux' true loc env1 p2 in
               (match uu____3994 with
                | (loc1,env2,var,p3,uu____4021) ->
                    let uu____4026 =
                      FStar_List.fold_left
                        (fun uu____4058  ->
                           fun p4  ->
                             match uu____4058 with
                             | (loc2,env3,ps1) ->
                                 let uu____4091 = aux' true loc2 env3 p4 in
                                 (match uu____4091 with
                                  | (loc3,env4,uu____4116,p5,uu____4118) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4026 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4169 ->
               let uu____4170 = aux' true loc env1 p1 in
               (match uu____4170 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4210 = aux_maybe_or env p in
         match uu____4210 with
         | (env1,b,pats) ->
             ((let uu____4241 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4241);
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
            let uu____4278 =
              let uu____4279 =
                let uu____4284 = FStar_ToSyntax_Env.qualify env x in
                (uu____4284, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4279 in
            (env, uu____4278, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4304 =
                  let uu____4305 =
                    let uu____4310 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4310, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4305 in
                mklet uu____4304
            | FStar_Parser_AST.PatVar (x,uu____4312) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4318);
                   FStar_Parser_AST.prange = uu____4319;_},t)
                ->
                let uu____4325 =
                  let uu____4326 =
                    let uu____4331 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4332 = desugar_term env t in
                    (uu____4331, uu____4332) in
                  LetBinder uu____4326 in
                (env, uu____4325, [])
            | uu____4335 ->
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4345 = desugar_data_pat env p is_mut in
             match uu____4345 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4374;
                       FStar_Syntax_Syntax.p = uu____4375;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4380;
                       FStar_Syntax_Syntax.p = uu____4381;_}::[] -> []
                   | uu____4386 -> p1 in
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
  fun uu____4393  ->
    fun env  ->
      fun pat  ->
        let uu____4396 = desugar_data_pat env pat false in
        match uu____4396 with | (env1,uu____4412,pat1) -> (env1, pat1)
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
      fun uu____4430  ->
        fun range  ->
          match uu____4430 with
          | (signedness,width) ->
              let uu____4438 = FStar_Const.bounds signedness width in
              (match uu____4438 with
               | (lower,upper) ->
                   let value =
                     let uu____4446 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4446 in
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
                      (let uu____4449 =
                         let uu____4450 =
                           let uu____4455 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____4455, range) in
                         FStar_Errors.Error uu____4450 in
                       FStar_Exn.raise uu____4449)
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
                       let uu____4463 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4463 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4473)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____4483 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____4483 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___254_4484 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___254_4484.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___254_4484.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4485 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4492 =
                             let uu____4493 =
                               let uu____4498 =
                                 FStar_Util.format1
                                   "Unexpected numeric literal.  Restart F* to load %s."
                                   tnm in
                               (uu____4498, range) in
                             FStar_Errors.Error uu____4493 in
                           FStar_Exn.raise uu____4492 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____4514 =
                       let uu____4517 =
                         let uu____4518 =
                           let uu____4533 =
                             let uu____4542 =
                               let uu____4549 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4549) in
                             [uu____4542] in
                           (lid1, uu____4533) in
                         FStar_Syntax_Syntax.Tm_app uu____4518 in
                       FStar_Syntax_Syntax.mk uu____4517 in
                     uu____4514 FStar_Pervasives_Native.None range)))
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
            let uu____4588 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4588 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4603 =
                    let uu____4604 =
                      let uu____4611 = mk_ref_read tm1 in
                      (uu____4611,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4604 in
                  FStar_All.pipe_left mk1 uu____4603
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4627 =
          let uu____4628 = unparen t in uu____4628.FStar_Parser_AST.tm in
        match uu____4627 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4629; FStar_Ident.ident = uu____4630;
              FStar_Ident.nsstr = uu____4631; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4634 ->
            let uu____4635 =
              let uu____4636 =
                let uu____4641 =
                  let uu____4642 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4642 in
                (uu____4641, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4636 in
            FStar_Exn.raise uu____4635 in
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
          let uu___255_4662 = e in
          {
            FStar_Syntax_Syntax.n = (uu___255_4662.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___255_4662.FStar_Syntax_Syntax.vars)
          } in
        let uu____4665 =
          let uu____4666 = unparen top in uu____4666.FStar_Parser_AST.tm in
        match uu____4665 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4667 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4718::uu____4719::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4723 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4723 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4736;_},t1::t2::[])
                  ->
                  let uu____4741 = flatten1 t1 in
                  FStar_List.append uu____4741 [t2]
              | uu____4744 -> [t] in
            let targs =
              let uu____4748 =
                let uu____4751 = unparen top in flatten1 uu____4751 in
              FStar_All.pipe_right uu____4748
                (FStar_List.map
                   (fun t  ->
                      let uu____4759 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4759)) in
            let uu____4760 =
              let uu____4765 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4765 in
            (match uu____4760 with
             | (tup,uu____4771) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4775 =
              let uu____4778 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4778 in
            FStar_All.pipe_left setpos uu____4775
        | FStar_Parser_AST.Uvar u ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4798 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____4798 with
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
                             let uu____4830 = desugar_term env t in
                             (uu____4830, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4844)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4859 =
              let uu___256_4860 = top in
              let uu____4861 =
                let uu____4862 =
                  let uu____4869 =
                    let uu___257_4870 = top in
                    let uu____4871 =
                      let uu____4872 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4872 in
                    {
                      FStar_Parser_AST.tm = uu____4871;
                      FStar_Parser_AST.range =
                        (uu___257_4870.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___257_4870.FStar_Parser_AST.level)
                    } in
                  (uu____4869, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4862 in
              {
                FStar_Parser_AST.tm = uu____4861;
                FStar_Parser_AST.range =
                  (uu___256_4860.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___256_4860.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4859
        | FStar_Parser_AST.Construct (n1,(a,uu____4875)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.warn top.FStar_Parser_AST.range
               "SMTPatT is deprecated; please just use SMTPat";
             (let uu____4891 =
                let uu___258_4892 = top in
                let uu____4893 =
                  let uu____4894 =
                    let uu____4901 =
                      let uu___259_4902 = top in
                      let uu____4903 =
                        let uu____4904 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____4904 in
                      {
                        FStar_Parser_AST.tm = uu____4903;
                        FStar_Parser_AST.range =
                          (uu___259_4902.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___259_4902.FStar_Parser_AST.level)
                      } in
                    (uu____4901, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____4894 in
                {
                  FStar_Parser_AST.tm = uu____4893;
                  FStar_Parser_AST.range =
                    (uu___258_4892.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___258_4892.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____4891))
        | FStar_Parser_AST.Construct (n1,(a,uu____4907)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4922 =
              let uu___260_4923 = top in
              let uu____4924 =
                let uu____4925 =
                  let uu____4932 =
                    let uu___261_4933 = top in
                    let uu____4934 =
                      let uu____4935 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4935 in
                    {
                      FStar_Parser_AST.tm = uu____4934;
                      FStar_Parser_AST.range =
                        (uu___261_4933.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___261_4933.FStar_Parser_AST.level)
                    } in
                  (uu____4932, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4925 in
              {
                FStar_Parser_AST.tm = uu____4924;
                FStar_Parser_AST.range =
                  (uu___260_4923.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___260_4923.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4922
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4936; FStar_Ident.ident = uu____4937;
              FStar_Ident.nsstr = uu____4938; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4941; FStar_Ident.ident = uu____4942;
              FStar_Ident.nsstr = uu____4943; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4946; FStar_Ident.ident = uu____4947;
               FStar_Ident.nsstr = uu____4948; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4966 =
              let uu____4967 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4967 in
            mk1 uu____4966
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4968; FStar_Ident.ident = uu____4969;
              FStar_Ident.nsstr = uu____4970; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4973; FStar_Ident.ident = uu____4974;
              FStar_Ident.nsstr = uu____4975; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4978; FStar_Ident.ident = uu____4979;
              FStar_Ident.nsstr = uu____4980; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4985;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____4987 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4987 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4992 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4992))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4996 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4996 with
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
                let uu____5023 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____5023 with
                | FStar_Pervasives_Native.Some uu____5032 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5037 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____5037 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5051 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5064 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____5064
              | uu____5065 ->
                  let uu____5072 =
                    let uu____5073 =
                      let uu____5078 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____5078, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5073 in
                  FStar_Exn.raise uu____5072))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5081 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5081 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5084 =
                    let uu____5085 =
                      let uu____5090 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5090, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5085 in
                  FStar_Exn.raise uu____5084
              | uu____5091 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5110 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5110 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5114 =
                    let uu____5121 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5121, true) in
                  (match uu____5114 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5136 ->
                            let uu____5143 =
                              FStar_Util.take
                                (fun uu____5167  ->
                                   match uu____5167 with
                                   | (uu____5172,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5143 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5236  ->
                                        match uu____5236 with
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
                    let uu____5279 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5279 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5282 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5289 =
              FStar_List.fold_left
                (fun uu____5334  ->
                   fun b  ->
                     match uu____5334 with
                     | (env1,tparams,typs) ->
                         let uu____5391 = desugar_binder env1 b in
                         (match uu____5391 with
                          | (xopt,t1) ->
                              let uu____5420 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5429 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5429)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5420 with
                               | (env2,x) ->
                                   let uu____5449 =
                                     let uu____5452 =
                                       let uu____5455 =
                                         let uu____5456 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5456 in
                                       [uu____5455] in
                                     FStar_List.append typs uu____5452 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___262_5482 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___262_5482.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___262_5482.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5449)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5289 with
             | (env1,uu____5506,targs) ->
                 let uu____5528 =
                   let uu____5533 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5533 in
                 (match uu____5528 with
                  | (tup,uu____5539) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5550 = uncurry binders t in
            (match uu____5550 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___229_5582 =
                   match uu___229_5582 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5596 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5596
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5618 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5618 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5633 = desugar_binder env b in
            (match uu____5633 with
             | (FStar_Pervasives_Native.None ,uu____5640) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5650 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5650 with
                  | ((x,uu____5656),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5663 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5663))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5683 =
              FStar_List.fold_left
                (fun uu____5703  ->
                   fun pat  ->
                     match uu____5703 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5729,t) ->
                              let uu____5731 =
                                let uu____5734 = free_type_vars env1 t in
                                FStar_List.append uu____5734 ftvs in
                              (env1, uu____5731)
                          | uu____5739 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5683 with
             | (uu____5744,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5756 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5756 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___230_5797 =
                   match uu___230_5797 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5835 =
                                 let uu____5836 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5836
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5835 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5889 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5889
                   | p::rest ->
                       let uu____5900 = desugar_binding_pat env1 p in
                       (match uu____5900 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5924 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5929 =
                              match b with
                              | LetBinder uu____5962 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6012) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6048 =
                                          let uu____6053 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____6053, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____6048
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6089,uu____6090) ->
                                             let tup2 =
                                               let uu____6092 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6092
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6096 =
                                                 let uu____6099 =
                                                   let uu____6100 =
                                                     let uu____6115 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6118 =
                                                       let uu____6121 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6122 =
                                                         let uu____6125 =
                                                           let uu____6126 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6126 in
                                                         [uu____6125] in
                                                       uu____6121 ::
                                                         uu____6122 in
                                                     (uu____6115, uu____6118) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6100 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6099 in
                                               uu____6096
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6137 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6137 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6168,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6170,pats)) ->
                                             let tupn =
                                               let uu____6209 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6209
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6219 =
                                                 let uu____6220 =
                                                   let uu____6235 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6238 =
                                                     let uu____6247 =
                                                       let uu____6256 =
                                                         let uu____6257 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6257 in
                                                       [uu____6256] in
                                                     FStar_List.append args
                                                       uu____6247 in
                                                   (uu____6235, uu____6238) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6220 in
                                               mk1 uu____6219 in
                                             let p2 =
                                               let uu____6277 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6277 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6312 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5929 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6379,uu____6380,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6394 =
                let uu____6395 = unparen e in uu____6395.FStar_Parser_AST.tm in
              match uu____6394 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6401 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6405 ->
            let rec aux args e =
              let uu____6437 =
                let uu____6438 = unparen e in uu____6438.FStar_Parser_AST.tm in
              match uu____6437 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6451 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6451 in
                  aux (arg :: args) e1
              | uu____6464 ->
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
              let uu____6490 =
                let uu____6491 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6491 in
              FStar_Parser_AST.mk_term uu____6490 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6492 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6492
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6495 =
              let uu____6496 =
                let uu____6503 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6503,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6496 in
            mk1 uu____6495
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6521 =
              let uu____6526 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6526 then desugar_typ else desugar_term in
            uu____6521 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6559 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6645  ->
                        match uu____6645 with
                        | (p,def) ->
                            let uu____6670 = is_app_pattern p in
                            if uu____6670
                            then
                              let uu____6689 =
                                destruct_app_pattern env top_level p in
                              (uu____6689, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6743 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6743, def1)
                               | uu____6772 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6798);
                                           FStar_Parser_AST.prange =
                                             uu____6799;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6823 =
                                            let uu____6838 =
                                              let uu____6843 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6843 in
                                            (uu____6838, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6823, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6890)
                                        ->
                                        if top_level
                                        then
                                          let uu____6913 =
                                            let uu____6928 =
                                              let uu____6933 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6933 in
                                            (uu____6928, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6913, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6979 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6998 =
                FStar_List.fold_left
                  (fun uu____7058  ->
                     fun uu____7059  ->
                       match (uu____7058, uu____7059) with
                       | ((env1,fnames,rec_bindings),((f,uu____7142,uu____7143),uu____7144))
                           ->
                           let uu____7223 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7249 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7249 with
                                  | (env2,xx) ->
                                      let uu____7268 =
                                        let uu____7271 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7271 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7268))
                             | FStar_Util.Inr l ->
                                 let uu____7279 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7279, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7223 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6998 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7405 =
                    match uu____7405 with
                    | ((uu____7428,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7472 = is_comp_type env1 t in
                                if uu____7472
                                then
                                  ((let uu____7474 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7484 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7484)) in
                                    match uu____7474 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7487 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7489 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7489))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7487
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7493 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7493 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7497 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7512 =
                                let uu____7513 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7513
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7512 in
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
                  let uu____7547 =
                    let uu____7548 =
                      let uu____7561 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7561) in
                    FStar_Syntax_Syntax.Tm_let uu____7548 in
                  FStar_All.pipe_left mk1 uu____7547 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7592 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7592 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7619 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7619
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
                    | LocalBinder (x,uu____7631) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7634;
                              FStar_Syntax_Syntax.p = uu____7635;_}::[] ->
                              body1
                          | uu____7640 ->
                              let uu____7643 =
                                let uu____7646 =
                                  let uu____7647 =
                                    let uu____7670 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7671 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7670, uu____7671) in
                                  FStar_Syntax_Syntax.Tm_match uu____7647 in
                                FStar_Syntax_Syntax.mk uu____7646 in
                              uu____7643 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7681 =
                          let uu____7682 =
                            let uu____7695 =
                              let uu____7696 =
                                let uu____7697 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7697] in
                              FStar_Syntax_Subst.close uu____7696 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7695) in
                          FStar_Syntax_Syntax.Tm_let uu____7682 in
                        FStar_All.pipe_left mk1 uu____7681 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____7723 = is_rec || (is_app_pattern pat) in
            if uu____7723
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____7732 =
                let uu____7733 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7733 in
              mk1 uu____7732 in
            let uu____7734 =
              let uu____7735 =
                let uu____7758 =
                  let uu____7761 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7761
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7782 =
                  let uu____7797 =
                    let uu____7810 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7813 = desugar_term env t2 in
                    (uu____7810, FStar_Pervasives_Native.None, uu____7813) in
                  let uu____7822 =
                    let uu____7837 =
                      let uu____7850 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7853 = desugar_term env t3 in
                      (uu____7850, FStar_Pervasives_Native.None, uu____7853) in
                    [uu____7837] in
                  uu____7797 :: uu____7822 in
                (uu____7758, uu____7782) in
              FStar_Syntax_Syntax.Tm_match uu____7735 in
            mk1 uu____7734
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
            let desugar_branch uu____7994 =
              match uu____7994 with
              | (pat,wopt,b) ->
                  let uu____8012 = desugar_match_pat env pat in
                  (match uu____8012 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8033 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____8033 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____8035 =
              let uu____8036 =
                let uu____8059 = desugar_term env e in
                let uu____8060 = FStar_List.collect desugar_branch branches in
                (uu____8059, uu____8060) in
              FStar_Syntax_Syntax.Tm_match uu____8036 in
            FStar_All.pipe_left mk1 uu____8035
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8089 = is_comp_type env t in
              if uu____8089
              then
                let uu____8096 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8096
              else
                (let uu____8102 = desugar_term env t in
                 FStar_Util.Inl uu____8102) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8108 =
              let uu____8109 =
                let uu____8136 = desugar_term env e in
                (uu____8136, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8109 in
            FStar_All.pipe_left mk1 uu____8108
        | FStar_Parser_AST.Record (uu____8161,[]) ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8198 = FStar_List.hd fields in
              match uu____8198 with | (f,uu____8210) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8252  ->
                        match uu____8252 with
                        | (g,uu____8258) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8264,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8278 =
                         let uu____8279 =
                           let uu____8284 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8284, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8279 in
                       FStar_Exn.raise uu____8278
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
                  let uu____8292 =
                    let uu____8303 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8334  ->
                              match uu____8334 with
                              | (f,uu____8344) ->
                                  let uu____8345 =
                                    let uu____8346 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8346 in
                                  (uu____8345, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8303) in
                  FStar_Parser_AST.Construct uu____8292
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8364 =
                      let uu____8365 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8365 in
                    FStar_Parser_AST.mk_term uu____8364 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8367 =
                      let uu____8380 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8410  ->
                                match uu____8410 with
                                | (f,uu____8420) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8380) in
                    FStar_Parser_AST.Record uu____8367 in
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
                         FStar_Syntax_Syntax.pos = uu____8448;
                         FStar_Syntax_Syntax.vars = uu____8449;_},args);
                    FStar_Syntax_Syntax.pos = uu____8451;
                    FStar_Syntax_Syntax.vars = uu____8452;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8480 =
                     let uu____8481 =
                       let uu____8496 =
                         let uu____8497 =
                           let uu____8500 =
                             let uu____8501 =
                               let uu____8508 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8508) in
                             FStar_Syntax_Syntax.Record_ctor uu____8501 in
                           FStar_Pervasives_Native.Some uu____8500 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8497 in
                       (uu____8496, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8481 in
                   FStar_All.pipe_left mk1 uu____8480 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8539 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8543 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8543 with
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
                  let uu____8562 =
                    let uu____8563 =
                      let uu____8578 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8579 =
                        let uu____8582 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8582] in
                      (uu____8578, uu____8579) in
                    FStar_Syntax_Syntax.Tm_app uu____8563 in
                  FStar_All.pipe_left mk1 uu____8562))
        | FStar_Parser_AST.NamedTyp (uu____8587,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8590 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8591 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8592,uu____8593,uu____8594) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8607,uu____8608,uu____8609) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8622,uu____8623,uu____8624) ->
            failwith "Not implemented yet"
and not_ascribed: FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8638 -> false
    | uu____8647 -> true
and is_synth_by_tactic:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8653 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8653 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8657 -> false
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
           (fun uu____8694  ->
              match uu____8694 with
              | (a,imp) ->
                  let uu____8707 = desugar_term env a in
                  arg_withimp_e imp uu____8707))
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
        let is_requires uu____8726 =
          match uu____8726 with
          | (t1,uu____8732) ->
              let uu____8733 =
                let uu____8734 = unparen t1 in uu____8734.FStar_Parser_AST.tm in
              (match uu____8733 with
               | FStar_Parser_AST.Requires uu____8735 -> true
               | uu____8742 -> false) in
        let is_ensures uu____8750 =
          match uu____8750 with
          | (t1,uu____8756) ->
              let uu____8757 =
                let uu____8758 = unparen t1 in uu____8758.FStar_Parser_AST.tm in
              (match uu____8757 with
               | FStar_Parser_AST.Ensures uu____8759 -> true
               | uu____8766 -> false) in
        let is_app head1 uu____8777 =
          match uu____8777 with
          | (t1,uu____8783) ->
              let uu____8784 =
                let uu____8785 = unparen t1 in uu____8785.FStar_Parser_AST.tm in
              (match uu____8784 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8787;
                      FStar_Parser_AST.level = uu____8788;_},uu____8789,uu____8790)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____8791 -> false) in
        let is_smt_pat uu____8799 =
          match uu____8799 with
          | (t1,uu____8805) ->
              let uu____8806 =
                let uu____8807 = unparen t1 in uu____8807.FStar_Parser_AST.tm in
              (match uu____8806 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8810);
                             FStar_Parser_AST.range = uu____8811;
                             FStar_Parser_AST.level = uu____8812;_},uu____8813)::uu____8814::[])
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
                             FStar_Parser_AST.range = uu____8853;
                             FStar_Parser_AST.level = uu____8854;_},uu____8855)::uu____8856::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____8881 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8909 = head_and_args t1 in
          match uu____8909 with
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
                   let thunk_ens uu____9003 =
                     match uu____9003 with
                     | (e,i) ->
                         let uu____9014 = thunk_ens_ e in (uu____9014, i) in
                   let fail_lemma uu____9024 =
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
                         let uu____9104 =
                           let uu____9111 =
                             let uu____9118 = thunk_ens ens in
                             [uu____9118; nil_pat] in
                           req_true :: uu____9111 in
                         unit_tm :: uu____9104
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9165 =
                           let uu____9172 =
                             let uu____9179 = thunk_ens ens in
                             [uu____9179; nil_pat] in
                           req :: uu____9172 in
                         unit_tm :: uu____9165
                     | ens::smtpat::[] when
                         (((let uu____9228 = is_requires ens in
                            Prims.op_Negation uu____9228) &&
                             (let uu____9230 = is_smt_pat ens in
                              Prims.op_Negation uu____9230))
                            &&
                            (let uu____9232 = is_decreases ens in
                             Prims.op_Negation uu____9232))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9233 =
                           let uu____9240 =
                             let uu____9247 = thunk_ens ens in
                             [uu____9247; smtpat] in
                           req_true :: uu____9240 in
                         unit_tm :: uu____9233
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9294 =
                           let uu____9301 =
                             let uu____9308 = thunk_ens ens in
                             [uu____9308; nil_pat; dec] in
                           req_true :: uu____9301 in
                         unit_tm :: uu____9294
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9368 =
                           let uu____9375 =
                             let uu____9382 = thunk_ens ens in
                             [uu____9382; smtpat; dec] in
                           req_true :: uu____9375 in
                         unit_tm :: uu____9368
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9442 =
                           let uu____9449 =
                             let uu____9456 = thunk_ens ens in
                             [uu____9456; nil_pat; dec] in
                           req :: uu____9449 in
                         unit_tm :: uu____9442
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9516 =
                           let uu____9523 =
                             let uu____9530 = thunk_ens ens in
                             [uu____9530; smtpat] in
                           req :: uu____9523 in
                         unit_tm :: uu____9516
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9595 =
                           let uu____9602 =
                             let uu____9609 = thunk_ens ens in
                             [uu____9609; dec; smtpat] in
                           req :: uu____9602 in
                         unit_tm :: uu____9595
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9671 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9671, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9699 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9699
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9717 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9717
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
               | uu____9755 ->
                   let default_effect =
                     let uu____9757 = FStar_Options.ml_ish () in
                     if uu____9757
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9760 =
                           FStar_Options.warn_default_effects () in
                         if uu____9760
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9784 = pre_process_comp_typ t in
        match uu____9784 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9833 =
                  let uu____9834 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9834 in
                fail uu____9833)
             else ();
             (let is_universe uu____9843 =
                match uu____9843 with
                | (uu____9848,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9850 = FStar_Util.take is_universe args in
              match uu____9850 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9909  ->
                         match uu____9909 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9916 =
                    let uu____9931 = FStar_List.hd args1 in
                    let uu____9940 = FStar_List.tl args1 in
                    (uu____9931, uu____9940) in
                  (match uu____9916 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9995 =
                         let is_decrease uu____10031 =
                           match uu____10031 with
                           | (t1,uu____10041) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10051;
                                       FStar_Syntax_Syntax.vars = uu____10052;_},uu____10053::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10084 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9995 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10198  ->
                                      match uu____10198 with
                                      | (t1,uu____10208) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10217,(arg,uu____10219)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10248 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10262 -> false in
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
                                           | uu____10410 -> pat in
                                         let uu____10411 =
                                           let uu____10422 =
                                             let uu____10433 =
                                               let uu____10442 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10442, aq) in
                                             [uu____10433] in
                                           ens :: uu____10422 in
                                         req :: uu____10411
                                     | uu____10483 -> rest2
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
        | uu____10505 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___263_10522 = t in
        {
          FStar_Syntax_Syntax.n = (uu___263_10522.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___263_10522.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___264_10556 = b in
             {
               FStar_Parser_AST.b = (uu___264_10556.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___264_10556.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___264_10556.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10615 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10615)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10628 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10628 with
             | (env1,a1) ->
                 let a2 =
                   let uu___265_10638 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___265_10638.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___265_10638.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10660 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10674 =
                     let uu____10677 =
                       let uu____10678 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10678] in
                     no_annot_abs uu____10677 body2 in
                   FStar_All.pipe_left setpos uu____10674 in
                 let uu____10683 =
                   let uu____10684 =
                     let uu____10699 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10700 =
                       let uu____10703 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10703] in
                     (uu____10699, uu____10700) in
                   FStar_Syntax_Syntax.Tm_app uu____10684 in
                 FStar_All.pipe_left mk1 uu____10683)
        | uu____10708 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____10780 = q (rest, pats, body) in
              let uu____10787 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10780 uu____10787
                FStar_Parser_AST.Formula in
            let uu____10788 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10788 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10797 -> failwith "impossible" in
      let uu____10800 =
        let uu____10801 = unparen f in uu____10801.FStar_Parser_AST.tm in
      match uu____10800 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10808,uu____10809) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10820,uu____10821) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10852 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10852
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10888 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10888
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____10931 -> desugar_term env f
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
      let uu____10936 =
        FStar_List.fold_left
          (fun uu____10972  ->
             fun b  ->
               match uu____10972 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___266_11024 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___266_11024.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___266_11024.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___266_11024.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11041 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____11041 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___267_11061 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___267_11061.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___267_11061.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11078 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10936 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____11165 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11165)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11170 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11170)
      | FStar_Parser_AST.TVariable x ->
          let uu____11174 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11174)
      | FStar_Parser_AST.NoName t ->
          let uu____11182 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11182)
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
               (fun uu___231_11218  ->
                  match uu___231_11218 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11219 -> false)) in
        let quals2 q =
          let uu____11230 =
            (let uu____11233 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11233) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11230
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11246 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11246;
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
            let uu____11282 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11312  ->
                        match uu____11312 with
                        | (x,uu____11320) ->
                            let uu____11321 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11321 with
                             | (field_name,uu____11329) ->
                                 let only_decl =
                                   ((let uu____11333 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11333)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11335 =
                                        let uu____11336 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11336.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11335) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11350 =
                                       FStar_List.filter
                                         (fun uu___232_11354  ->
                                            match uu___232_11354 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11355 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11350
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___233_11368  ->
                                             match uu___233_11368 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11369 -> false)) in
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
                                      let uu____11377 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11377
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11382 =
                                        let uu____11387 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11387 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11382;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11389 =
                                        let uu____11390 =
                                          let uu____11397 =
                                            let uu____11400 =
                                              let uu____11401 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11401
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11400] in
                                          ((false, [lb]), uu____11397) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11390 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11389;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11282 FStar_List.flatten
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
            (lid,uu____11448,t,uu____11450,n1,uu____11452) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11457 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11457 with
             | (formals,uu____11473) ->
                 (match formals with
                  | [] -> []
                  | uu____11496 ->
                      let filter_records uu___234_11508 =
                        match uu___234_11508 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11511,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11523 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11525 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11525 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11535 = FStar_Util.first_N n1 formals in
                      (match uu____11535 with
                       | (uu____11558,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11584 -> []
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
                    let uu____11642 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11642
                    then
                      let uu____11645 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11645
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11648 =
                      let uu____11653 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11653 in
                    let uu____11654 =
                      let uu____11657 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11657 in
                    let uu____11660 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11648;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11654;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11660
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
          let tycon_id uu___235_11709 =
            match uu___235_11709 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11711,uu____11712) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11722,uu____11723,uu____11724) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11734,uu____11735,uu____11736) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____11766,uu____11767,uu____11768) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11810) ->
                let uu____11811 =
                  let uu____11812 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11812 in
                FStar_Parser_AST.mk_term uu____11811 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11814 =
                  let uu____11815 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11815 in
                FStar_Parser_AST.mk_term uu____11814 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11817) ->
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
              | uu____11840 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11846 =
                     let uu____11847 =
                       let uu____11854 = binder_to_term b in
                       (out, uu____11854, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11847 in
                   FStar_Parser_AST.mk_term uu____11846
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___236_11864 =
            match uu___236_11864 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____11919  ->
                       match uu____11919 with
                       | (x,t,uu____11930) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____11936 =
                    let uu____11937 =
                      let uu____11938 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11938 in
                    FStar_Parser_AST.mk_term uu____11937
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11936 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11942 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11969  ->
                          match uu____11969 with
                          | (x,uu____11979,uu____11980) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____11942)
            | uu____12033 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___237_12064 =
            match uu___237_12064 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____12088 = typars_of_binders _env binders in
                (match uu____12088 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12134 =
                         let uu____12135 =
                           let uu____12136 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12136 in
                         FStar_Parser_AST.mk_term uu____12135
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12134 binders in
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
            | uu____12149 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12193 =
              FStar_List.fold_left
                (fun uu____12233  ->
                   fun uu____12234  ->
                     match (uu____12233, uu____12234) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12325 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12325 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12193 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12438 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12438
                | uu____12439 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12447 = desugar_abstract_tc quals env [] tc in
              (match uu____12447 with
               | (uu____12460,uu____12461,se,uu____12463) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12466,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12483 =
                                 let uu____12484 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12484 in
                               if uu____12483
                               then
                                 let uu____12485 =
                                   let uu____12486 =
                                     FStar_Syntax_Print.lid_to_string l in
                                   FStar_Util.format1
                                     "Adding an implicit 'assume new' qualifier on %s"
                                     uu____12486 in
                                 FStar_Errors.warn
                                   se.FStar_Syntax_Syntax.sigrng uu____12485
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12493 ->
                               let uu____12494 =
                                 let uu____12497 =
                                   let uu____12498 =
                                     let uu____12511 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12511) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12498 in
                                 FStar_Syntax_Syntax.mk uu____12497 in
                               uu____12494 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___268_12515 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___268_12515.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___268_12515.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___268_12515.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12518 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12521 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12521
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12536 = typars_of_binders env binders in
              (match uu____12536 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12572 =
                           FStar_Util.for_some
                             (fun uu___238_12574  ->
                                match uu___238_12574 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12575 -> false) quals in
                         if uu____12572
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12582 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___239_12586  ->
                               match uu___239_12586 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12587 -> false)) in
                     if uu____12582
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12596 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12596
                     then
                       let uu____12599 =
                         let uu____12606 =
                           let uu____12607 = unparen t in
                           uu____12607.FStar_Parser_AST.tm in
                         match uu____12606 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12628 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12658)::args_rev ->
                                   let uu____12670 =
                                     let uu____12671 = unparen last_arg in
                                     uu____12671.FStar_Parser_AST.tm in
                                   (match uu____12670 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12699 -> ([], args))
                               | uu____12708 -> ([], args) in
                             (match uu____12628 with
                              | (cattributes,args1) ->
                                  let uu____12747 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12747))
                         | uu____12758 -> (t, []) in
                       match uu____12599 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___240_12780  ->
                                     match uu___240_12780 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____12781 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____12792)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12816 = tycon_record_as_variant trec in
              (match uu____12816 with
               | (t,fs) ->
                   let uu____12833 =
                     let uu____12836 =
                       let uu____12837 =
                         let uu____12846 =
                           let uu____12849 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12849 in
                         (uu____12846, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12837 in
                     uu____12836 :: quals in
                   desugar_tycon env d uu____12833 [t])
          | uu____12854::uu____12855 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____13016 = et in
                match uu____13016 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13241 ->
                         let trec = tc in
                         let uu____13265 = tycon_record_as_variant trec in
                         (match uu____13265 with
                          | (t,fs) ->
                              let uu____13324 =
                                let uu____13327 =
                                  let uu____13328 =
                                    let uu____13337 =
                                      let uu____13340 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13340 in
                                    (uu____13337, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13328 in
                                uu____13327 :: quals1 in
                              collect_tcs uu____13324 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13427 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13427 with
                          | (env2,uu____13487,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13636 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13636 with
                          | (env2,uu____13696,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13821 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13868 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13868 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___242_14379  ->
                             match uu___242_14379 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14446,uu____14447);
                                    FStar_Syntax_Syntax.sigrng = uu____14448;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14449;
                                    FStar_Syntax_Syntax.sigmeta = uu____14450;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14451;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14512 =
                                     typars_of_binders env1 binders in
                                   match uu____14512 with
                                   | (env2,tpars1) ->
                                       let uu____14543 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14543 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14576 =
                                   let uu____14597 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14597) in
                                 [uu____14576]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14665);
                                    FStar_Syntax_Syntax.sigrng = uu____14666;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14668;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14669;_},constrs,tconstr,quals1)
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
                                 let uu____14765 = push_tparams env1 tpars in
                                 (match uu____14765 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14842  ->
                                             match uu____14842 with
                                             | (x,uu____14856) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14864 =
                                        let uu____14893 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15007  ->
                                                  match uu____15007 with
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
                                                        let uu____15063 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____15063 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___241_15074
                                                                 ->
                                                                match uu___241_15074
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15086
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____15094 =
                                                        let uu____15115 =
                                                          let uu____15116 =
                                                            let uu____15117 =
                                                              let uu____15132
                                                                =
                                                                let uu____15135
                                                                  =
                                                                  let uu____15138
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15138 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15135 in
                                                              (name, univs1,
                                                                uu____15132,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15117 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15116;
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
                                                          uu____15115) in
                                                      (name, uu____15094))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14893 in
                                      (match uu____14864 with
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
                             | uu____15377 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15509  ->
                             match uu____15509 with
                             | (name_doc,uu____15537,uu____15538) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15618  ->
                             match uu____15618 with
                             | (uu____15639,uu____15640,se) -> se)) in
                   let uu____15670 =
                     let uu____15677 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15677 rng in
                   (match uu____15670 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____15743  ->
                                  match uu____15743 with
                                  | (uu____15766,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15817,tps,k,uu____15820,constrs)
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
                                  | uu____15839 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15856  ->
                                 match uu____15856 with
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
      let uu____15893 =
        FStar_List.fold_left
          (fun uu____15916  ->
             fun b  ->
               match uu____15916 with
               | (env1,binders1) ->
                   let uu____15936 = desugar_binder env1 b in
                   (match uu____15936 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15953 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15953 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15970 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____15893 with
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
                let uu____16088 = desugar_binders monad_env eff_binders in
                match uu____16088 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16109 =
                        let uu____16110 =
                          let uu____16117 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16117 in
                        FStar_List.length uu____16110 in
                      uu____16109 = (Prims.parse_int "1") in
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
                          (uu____16159,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16161,uu____16162,uu____16163),uu____16164)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16197 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16198 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16210 = name_of_eff_decl decl in
                           FStar_List.mem uu____16210 mandatory_members)
                        eff_decls in
                    (match uu____16198 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16227 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16256  ->
                                   fun decl  ->
                                     match uu____16256 with
                                     | (env2,out) ->
                                         let uu____16276 =
                                           desugar_decl env2 decl in
                                         (match uu____16276 with
                                          | (env3,ses) ->
                                              let uu____16289 =
                                                let uu____16292 =
                                                  FStar_List.hd ses in
                                                uu____16292 :: out in
                                              (env3, uu____16289)))
                                (env1, [])) in
                         (match uu____16227 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16360,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16363,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16364,
                                                                (def,uu____16366)::
                                                                (cps_type,uu____16368)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16369;
                                                             FStar_Parser_AST.level
                                                               = uu____16370;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16422 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16422 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16442 =
                                                   let uu____16443 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16444 =
                                                     let uu____16445 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16445 in
                                                   let uu____16450 =
                                                     let uu____16451 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16451 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16443;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16444;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16450
                                                   } in
                                                 (uu____16442, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16458,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16461,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16496 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16496 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16516 =
                                                   let uu____16517 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16518 =
                                                     let uu____16519 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16519 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16517;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16518;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16516, doc1))
                                        | uu____16526 ->
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
                                let uu____16556 =
                                  let uu____16557 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16557 in
                                ([], uu____16556) in
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
                                    let uu____16574 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16574) in
                                  let uu____16581 =
                                    let uu____16582 =
                                      let uu____16583 =
                                        let uu____16584 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16584 in
                                      let uu____16593 = lookup "return" in
                                      let uu____16594 = lookup "bind" in
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
                                          uu____16583;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16593;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16594;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16582 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16581;
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
                                       (fun uu___243_16598  ->
                                          match uu___243_16598 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16599 -> true
                                          | uu____16600 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16610 =
                                     let uu____16611 =
                                       let uu____16612 = lookup "return_wp" in
                                       let uu____16613 = lookup "bind_wp" in
                                       let uu____16614 =
                                         lookup "if_then_else" in
                                       let uu____16615 = lookup "ite_wp" in
                                       let uu____16616 = lookup "stronger" in
                                       let uu____16617 = lookup "close_wp" in
                                       let uu____16618 = lookup "assert_p" in
                                       let uu____16619 = lookup "assume_p" in
                                       let uu____16620 = lookup "null_wp" in
                                       let uu____16621 = lookup "trivial" in
                                       let uu____16622 =
                                         if rr
                                         then
                                           let uu____16623 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16623
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16639 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16641 =
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
                                           uu____16612;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16613;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16614;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16615;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16616;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16617;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16618;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16619;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16620;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16621;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16622;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16639;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16641;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16611 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16610;
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
                                        fun uu____16666  ->
                                          match uu____16666 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16680 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16680 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16682 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16682
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
                let uu____16713 = desugar_binders env1 eff_binders in
                match uu____16713 with
                | (env2,binders) ->
                    let uu____16732 =
                      let uu____16751 = head_and_args defn in
                      match uu____16751 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16796 ->
                                let uu____16797 =
                                  let uu____16798 =
                                    let uu____16803 =
                                      let uu____16804 =
                                        let uu____16805 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____16805 " not found" in
                                      Prims.strcat "Effect " uu____16804 in
                                    (uu____16803,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16798 in
                                FStar_Exn.raise uu____16797 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16807 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16837)::args_rev ->
                                let uu____16849 =
                                  let uu____16850 = unparen last_arg in
                                  uu____16850.FStar_Parser_AST.tm in
                                (match uu____16849 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16878 -> ([], args))
                            | uu____16887 -> ([], args) in
                          (match uu____16807 with
                           | (cattributes,args1) ->
                               let uu____16938 = desugar_args env2 args1 in
                               let uu____16947 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16938, uu____16947)) in
                    (match uu____16732 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____17006 =
                           match uu____17006 with
                           | (uu____17019,x) ->
                               let uu____17025 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____17025 with
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
                                      let uu____17051 =
                                        let uu____17052 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____17052 in
                                      ([], uu____17051)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____17057 =
                             let uu____17058 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____17058 in
                           let uu____17069 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17070 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17071 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17072 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17073 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____17074 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17075 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17076 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17077 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17078 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____17079 =
                             let uu____17080 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____17080 in
                           let uu____17091 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17092 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17093 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____17101 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____17102 =
                                    let uu____17103 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____17103 in
                                  let uu____17114 =
                                    let uu____17115 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____17115 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____17101;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____17102;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____17114
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____17057;
                             FStar_Syntax_Syntax.ret_wp = uu____17069;
                             FStar_Syntax_Syntax.bind_wp = uu____17070;
                             FStar_Syntax_Syntax.if_then_else = uu____17071;
                             FStar_Syntax_Syntax.ite_wp = uu____17072;
                             FStar_Syntax_Syntax.stronger = uu____17073;
                             FStar_Syntax_Syntax.close_wp = uu____17074;
                             FStar_Syntax_Syntax.assert_p = uu____17075;
                             FStar_Syntax_Syntax.assume_p = uu____17076;
                             FStar_Syntax_Syntax.null_wp = uu____17077;
                             FStar_Syntax_Syntax.trivial = uu____17078;
                             FStar_Syntax_Syntax.repr = uu____17079;
                             FStar_Syntax_Syntax.return_repr = uu____17091;
                             FStar_Syntax_Syntax.bind_repr = uu____17092;
                             FStar_Syntax_Syntax.actions = uu____17093
                           } in
                         let se =
                           let for_free =
                             let uu____17128 =
                               let uu____17129 =
                                 let uu____17136 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____17136 in
                               FStar_List.length uu____17129 in
                             uu____17128 = (Prims.parse_int "1") in
                           let uu____17165 =
                             let uu____17168 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____17168 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____17165;
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
                                       let uu____17188 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____17188 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____17190 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____17190
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
    let uu____17205 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____17205 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17256 ->
              let uu____17257 =
                let uu____17258 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17258 in
              Prims.strcat "\n  " uu____17257
          | uu____17259 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____17272  ->
               match uu____17272 with
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
          let uu____17290 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____17290
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____17292 =
          let uu____17301 = FStar_Syntax_Syntax.as_arg arg in [uu____17301] in
        FStar_Syntax_Util.mk_app fv uu____17292
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17308 = desugar_decl_noattrs env d in
      match uu____17308 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____17328 = mk_comment_attr d in uu____17328 :: attrs1 in
          let uu____17333 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___269_17339 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___269_17339.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___269_17339.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___269_17339.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___269_17339.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____17333)
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
      | FStar_Parser_AST.Fsdoc uu____17365 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17381 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17381, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17420  ->
                 match uu____17420 with | (x,uu____17428) -> x) tcs in
          let uu____17433 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17433 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17455;
                    FStar_Parser_AST.prange = uu____17456;_},uu____17457)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17466;
                    FStar_Parser_AST.prange = uu____17467;_},uu____17468)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17483;
                         FStar_Parser_AST.prange = uu____17484;_},uu____17485);
                    FStar_Parser_AST.prange = uu____17486;_},uu____17487)::[]
                   -> false
               | (p,uu____17503)::[] ->
                   let uu____17512 = is_app_pattern p in
                   Prims.op_Negation uu____17512
               | uu____17513 -> false) in
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
            let uu____17532 =
              let uu____17533 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17533.FStar_Syntax_Syntax.n in
            (match uu____17532 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17541) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17574::uu____17575 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17578 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___244_17591  ->
                               match uu___244_17591 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17594;
                                   FStar_Syntax_Syntax.lbunivs = uu____17595;
                                   FStar_Syntax_Syntax.lbtyp = uu____17596;
                                   FStar_Syntax_Syntax.lbeff = uu____17597;
                                   FStar_Syntax_Syntax.lbdef = uu____17598;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17606;
                                   FStar_Syntax_Syntax.lbtyp = uu____17607;
                                   FStar_Syntax_Syntax.lbeff = uu____17608;
                                   FStar_Syntax_Syntax.lbdef = uu____17609;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17619 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17633  ->
                             match uu____17633 with
                             | (uu____17638,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17619
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17650 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17650
                   then
                     let uu____17659 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___270_17673 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___271_17675 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___271_17675.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___271_17675.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___270_17673.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___270_17673.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___270_17673.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___270_17673.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17659)
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
             | uu____17707 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17713 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17732 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17713 with
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
                       let uu___272_17756 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___272_17756.FStar_Parser_AST.prange)
                       }
                   | uu____17757 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___273_17764 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___273_17764.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___273_17764.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___273_17764.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17796 id =
                   match uu____17796 with
                   | (env1,ses) ->
                       let main =
                         let uu____17817 =
                           let uu____17818 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17818 in
                         FStar_Parser_AST.mk_term uu____17817
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
                       let uu____17868 = desugar_decl env1 id_decl in
                       (match uu____17868 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17886 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17886 FStar_Util.set_elements in
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
            let uu____17917 = close_fun env t in desugar_term env uu____17917 in
          let quals1 =
            let uu____17921 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17921
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____17927 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17927;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17939 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____17939 with
           | (t,uu____17953) ->
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
            let uu____17987 =
              let uu____17994 = FStar_Syntax_Syntax.null_binder t in
              [uu____17994] in
            let uu____17995 =
              let uu____17998 =
                let uu____17999 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17999 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17998 in
            FStar_Syntax_Util.arrow uu____17987 uu____17995 in
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
            let uu____18061 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____18061 with
            | FStar_Pervasives_Native.None  ->
                let uu____18064 =
                  let uu____18065 =
                    let uu____18070 =
                      let uu____18071 =
                        let uu____18072 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____18072 " not found" in
                      Prims.strcat "Effect name " uu____18071 in
                    (uu____18070, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____18065 in
                FStar_Exn.raise uu____18064
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____18076 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18118 =
                  let uu____18127 =
                    let uu____18134 = desugar_term env t in ([], uu____18134) in
                  FStar_Pervasives_Native.Some uu____18127 in
                (uu____18118, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18167 =
                  let uu____18176 =
                    let uu____18183 = desugar_term env wp in
                    ([], uu____18183) in
                  FStar_Pervasives_Native.Some uu____18176 in
                let uu____18192 =
                  let uu____18201 =
                    let uu____18208 = desugar_term env t in ([], uu____18208) in
                  FStar_Pervasives_Native.Some uu____18201 in
                (uu____18167, uu____18192)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18234 =
                  let uu____18243 =
                    let uu____18250 = desugar_term env t in ([], uu____18250) in
                  FStar_Pervasives_Native.Some uu____18243 in
                (FStar_Pervasives_Native.None, uu____18234) in
          (match uu____18076 with
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
      let uu____18340 =
        FStar_List.fold_left
          (fun uu____18360  ->
             fun d  ->
               match uu____18360 with
               | (env1,sigelts) ->
                   let uu____18380 = desugar_decl env1 d in
                   (match uu____18380 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____18340 with
      | (env1,sigelts) ->
          let rec forward acc uu___246_18421 =
            match uu___246_18421 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18435,FStar_Syntax_Syntax.Sig_let uu____18436) ->
                     let uu____18449 =
                       let uu____18452 =
                         let uu___274_18453 = se2 in
                         let uu____18454 =
                           let uu____18457 =
                             FStar_List.filter
                               (fun uu___245_18471  ->
                                  match uu___245_18471 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18475;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18476;_},uu____18477);
                                      FStar_Syntax_Syntax.pos = uu____18478;
                                      FStar_Syntax_Syntax.vars = uu____18479;_}
                                      when
                                      let uu____18502 =
                                        let uu____18503 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____18503 in
                                      uu____18502 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18504 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____18457
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___274_18453.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___274_18453.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___274_18453.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___274_18453.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18454
                         } in
                       uu____18452 :: se1 :: acc in
                     forward uu____18449 sigelts1
                 | uu____18509 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____18517 = forward [] sigelts in (env1, uu____18517)
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
          | (FStar_Pervasives_Native.None ,uu____18571) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18575;
               FStar_Syntax_Syntax.exports = uu____18576;
               FStar_Syntax_Syntax.is_interface = uu____18577;_},FStar_Parser_AST.Module
             (current_lid,uu____18579)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18587) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18590 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18626 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18626, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18643 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18643, mname, decls, false) in
        match uu____18590 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18673 = desugar_decls env2 decls in
            (match uu____18673 with
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
          let uu____18731 =
            (FStar_Options.interactive ()) &&
              (let uu____18733 =
                 let uu____18734 =
                   let uu____18735 = FStar_Options.file_list () in
                   FStar_List.hd uu____18735 in
                 FStar_Util.get_file_extension uu____18734 in
               FStar_List.mem uu____18733 ["fsti"; "fsi"]) in
          if uu____18731 then as_interface m else m in
        let uu____18739 = desugar_modul_common curmod env m1 in
        match uu____18739 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18754 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18772 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18772 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18788 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18788
            then
              let uu____18789 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18789
            else ());
           (let uu____18791 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18791, modul)))
let ast_modul_to_modul:
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____18806 = desugar_modul env modul in
      match uu____18806 with | (env1,modul1) -> (modul1, env1)
let decls_to_sigelts:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____18834 = desugar_decls env decls in
      match uu____18834 with | (env1,sigelts) -> (sigelts, env1)
let partial_ast_modul_to_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____18874 = desugar_partial_modul modul env a_modul in
        match uu____18874 with | (env1,modul1) -> (modul1, env1)
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun m  ->
    fun mii  ->
      fun en  ->
        let uu____18902 =
          FStar_ToSyntax_Env.prepare_module_or_interface false false en
            m.FStar_Syntax_Syntax.name mii in
        match uu____18902 with
        | (en1,pop_when_done) ->
            let en2 =
              let uu____18914 =
                FStar_ToSyntax_Env.set_current_module en1
                  m.FStar_Syntax_Syntax.name in
              FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18914
                m.FStar_Syntax_Syntax.exports in
            let env = FStar_ToSyntax_Env.finish en2 m in
            let uu____18916 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  m.FStar_Syntax_Syntax.name env
              else env in
            ((), uu____18916)