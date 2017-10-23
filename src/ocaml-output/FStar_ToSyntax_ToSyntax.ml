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
                          let uu___248_2717 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___249_2722 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___249_2722.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___249_2722.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___248_2717.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___250_2724 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___251_2729 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___251_2729.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___251_2729.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___250_2724.FStar_Syntax_Syntax.p)
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
                                 ((let uu___252_2774 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___252_2774.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___252_2774.FStar_Syntax_Syntax.index);
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
                                let uu___253_3889 = fv in
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
                                    (uu___253_3889.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___253_3889.FStar_Syntax_Syntax.fv_delta);
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
                                let uu___254_4466 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___254_4466.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___254_4466.FStar_Syntax_Syntax.vars)
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
          let uu___255_4644 = e in
          {
            FStar_Syntax_Syntax.n = (uu___255_4644.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___255_4644.FStar_Syntax_Syntax.vars)
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
              let uu___256_4842 = top in
              let uu____4843 =
                let uu____4844 =
                  let uu____4851 =
                    let uu___257_4852 = top in
                    let uu____4853 =
                      let uu____4854 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4854 in
                    {
                      FStar_Parser_AST.tm = uu____4853;
                      FStar_Parser_AST.range =
                        (uu___257_4852.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___257_4852.FStar_Parser_AST.level)
                    } in
                  (uu____4851, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4844 in
              {
                FStar_Parser_AST.tm = uu____4843;
                FStar_Parser_AST.range =
                  (uu___256_4842.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___256_4842.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4841
        | FStar_Parser_AST.Construct (n1,(a,uu____4857)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.warn top.FStar_Parser_AST.range
               "SMTPatT is deprecated; please just use SMTPat";
             (let uu____4873 =
                let uu___258_4874 = top in
                let uu____4875 =
                  let uu____4876 =
                    let uu____4883 =
                      let uu___259_4884 = top in
                      let uu____4885 =
                        let uu____4886 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____4886 in
                      {
                        FStar_Parser_AST.tm = uu____4885;
                        FStar_Parser_AST.range =
                          (uu___259_4884.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___259_4884.FStar_Parser_AST.level)
                      } in
                    (uu____4883, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____4876 in
                {
                  FStar_Parser_AST.tm = uu____4875;
                  FStar_Parser_AST.range =
                    (uu___258_4874.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___258_4874.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____4873))
        | FStar_Parser_AST.Construct (n1,(a,uu____4889)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4904 =
              let uu___260_4905 = top in
              let uu____4906 =
                let uu____4907 =
                  let uu____4914 =
                    let uu___261_4915 = top in
                    let uu____4916 =
                      let uu____4917 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4917 in
                    {
                      FStar_Parser_AST.tm = uu____4916;
                      FStar_Parser_AST.range =
                        (uu___261_4915.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___261_4915.FStar_Parser_AST.level)
                    } in
                  (uu____4914, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4907 in
              {
                FStar_Parser_AST.tm = uu____4906;
                FStar_Parser_AST.range =
                  (uu___260_4905.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___260_4905.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4904
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4918; FStar_Ident.ident = uu____4919;
              FStar_Ident.nsstr = uu____4920; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4923; FStar_Ident.ident = uu____4924;
              FStar_Ident.nsstr = uu____4925; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4928; FStar_Ident.ident = uu____4929;
               FStar_Ident.nsstr = uu____4930; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4948 =
              let uu____4949 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4949 in
            mk1 uu____4948
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4950; FStar_Ident.ident = uu____4951;
              FStar_Ident.nsstr = uu____4952; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4955; FStar_Ident.ident = uu____4956;
              FStar_Ident.nsstr = uu____4957; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4960; FStar_Ident.ident = uu____4961;
              FStar_Ident.nsstr = uu____4962; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4967;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____4969 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4969 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4974 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4974))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4978 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4978 with
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
                let uu____5005 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____5005 with
                | FStar_Pervasives_Native.Some uu____5014 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5019 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____5019 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5033 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5046 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____5046
              | uu____5047 ->
                  let uu____5054 =
                    let uu____5055 =
                      let uu____5060 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____5060, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5055 in
                  FStar_Exn.raise uu____5054))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5063 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5063 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5066 =
                    let uu____5067 =
                      let uu____5072 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5072, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5067 in
                  FStar_Exn.raise uu____5066
              | uu____5073 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5092 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5092 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5096 =
                    let uu____5103 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5103, true) in
                  (match uu____5096 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5118 ->
                            let uu____5125 =
                              FStar_Util.take
                                (fun uu____5149  ->
                                   match uu____5149 with
                                   | (uu____5154,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5125 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5218  ->
                                        match uu____5218 with
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
                    let uu____5261 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5261 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5264 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5271 =
              FStar_List.fold_left
                (fun uu____5316  ->
                   fun b  ->
                     match uu____5316 with
                     | (env1,tparams,typs) ->
                         let uu____5373 = desugar_binder env1 b in
                         (match uu____5373 with
                          | (xopt,t1) ->
                              let uu____5402 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5411 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5411)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5402 with
                               | (env2,x) ->
                                   let uu____5431 =
                                     let uu____5434 =
                                       let uu____5437 =
                                         let uu____5438 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5438 in
                                       [uu____5437] in
                                     FStar_List.append typs uu____5434 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___262_5464 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___262_5464.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___262_5464.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5431)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5271 with
             | (env1,uu____5488,targs) ->
                 let uu____5510 =
                   let uu____5515 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5515 in
                 (match uu____5510 with
                  | (tup,uu____5521) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5532 = uncurry binders t in
            (match uu____5532 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___229_5564 =
                   match uu___229_5564 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5578 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5578
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5600 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5600 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5615 = desugar_binder env b in
            (match uu____5615 with
             | (FStar_Pervasives_Native.None ,uu____5622) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5632 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5632 with
                  | ((x,uu____5638),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5645 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5645))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5665 =
              FStar_List.fold_left
                (fun uu____5685  ->
                   fun pat  ->
                     match uu____5685 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5711,t) ->
                              let uu____5713 =
                                let uu____5716 = free_type_vars env1 t in
                                FStar_List.append uu____5716 ftvs in
                              (env1, uu____5713)
                          | uu____5721 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5665 with
             | (uu____5726,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5738 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5738 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___230_5779 =
                   match uu___230_5779 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5817 =
                                 let uu____5818 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5818
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5817 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5871 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5871
                   | p::rest ->
                       let uu____5882 = desugar_binding_pat env1 p in
                       (match uu____5882 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5906 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5911 =
                              match b with
                              | LetBinder uu____5944 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____5994) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6030 =
                                          let uu____6035 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____6035, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____6030
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6071,uu____6072) ->
                                             let tup2 =
                                               let uu____6074 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6074
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6078 =
                                                 let uu____6081 =
                                                   let uu____6082 =
                                                     let uu____6097 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6100 =
                                                       let uu____6103 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6104 =
                                                         let uu____6107 =
                                                           let uu____6108 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6108 in
                                                         [uu____6107] in
                                                       uu____6103 ::
                                                         uu____6104 in
                                                     (uu____6097, uu____6100) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6082 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6081 in
                                               uu____6078
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6119 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6119 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6150,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6152,pats)) ->
                                             let tupn =
                                               let uu____6191 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6191
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6201 =
                                                 let uu____6202 =
                                                   let uu____6217 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6220 =
                                                     let uu____6229 =
                                                       let uu____6238 =
                                                         let uu____6239 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6239 in
                                                       [uu____6238] in
                                                     FStar_List.append args
                                                       uu____6229 in
                                                   (uu____6217, uu____6220) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6202 in
                                               mk1 uu____6201 in
                                             let p2 =
                                               let uu____6259 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6259 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6294 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5911 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6361,uu____6362,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6376 =
                let uu____6377 = unparen e in uu____6377.FStar_Parser_AST.tm in
              match uu____6376 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6383 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6387 ->
            let rec aux args e =
              let uu____6419 =
                let uu____6420 = unparen e in uu____6420.FStar_Parser_AST.tm in
              match uu____6419 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6433 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6433 in
                  aux (arg :: args) e1
              | uu____6446 ->
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
              let uu____6472 =
                let uu____6473 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6473 in
              FStar_Parser_AST.mk_term uu____6472 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6474 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6474
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6477 =
              let uu____6478 =
                let uu____6485 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6485,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6478 in
            mk1 uu____6477
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6503 =
              let uu____6508 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6508 then desugar_typ else desugar_term in
            uu____6503 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6541 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6627  ->
                        match uu____6627 with
                        | (p,def) ->
                            let uu____6652 = is_app_pattern p in
                            if uu____6652
                            then
                              let uu____6671 =
                                destruct_app_pattern env top_level p in
                              (uu____6671, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6725 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6725, def1)
                               | uu____6754 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6780);
                                           FStar_Parser_AST.prange =
                                             uu____6781;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6805 =
                                            let uu____6820 =
                                              let uu____6825 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6825 in
                                            (uu____6820, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6805, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6872)
                                        ->
                                        if top_level
                                        then
                                          let uu____6895 =
                                            let uu____6910 =
                                              let uu____6915 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6915 in
                                            (uu____6910, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6895, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6961 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6980 =
                FStar_List.fold_left
                  (fun uu____7040  ->
                     fun uu____7041  ->
                       match (uu____7040, uu____7041) with
                       | ((env1,fnames,rec_bindings),((f,uu____7124,uu____7125),uu____7126))
                           ->
                           let uu____7205 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7231 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7231 with
                                  | (env2,xx) ->
                                      let uu____7250 =
                                        let uu____7253 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7253 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7250))
                             | FStar_Util.Inr l ->
                                 let uu____7261 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7261, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7205 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6980 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7387 =
                    match uu____7387 with
                    | ((uu____7410,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7454 = is_comp_type env1 t in
                                if uu____7454
                                then
                                  ((let uu____7456 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7466 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7466)) in
                                    match uu____7456 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7469 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7471 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7471))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7469
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7475 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7475 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7479 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7494 =
                                let uu____7495 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7495
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7494 in
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
                  let uu____7529 =
                    let uu____7530 =
                      let uu____7543 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7543) in
                    FStar_Syntax_Syntax.Tm_let uu____7530 in
                  FStar_All.pipe_left mk1 uu____7529 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7574 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7574 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7601 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7601
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
                    | LocalBinder (x,uu____7613) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7616;
                              FStar_Syntax_Syntax.p = uu____7617;_}::[] ->
                              body1
                          | uu____7622 ->
                              let uu____7625 =
                                let uu____7628 =
                                  let uu____7629 =
                                    let uu____7652 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7653 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7652, uu____7653) in
                                  FStar_Syntax_Syntax.Tm_match uu____7629 in
                                FStar_Syntax_Syntax.mk uu____7628 in
                              uu____7625 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7663 =
                          let uu____7664 =
                            let uu____7677 =
                              let uu____7678 =
                                let uu____7679 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7679] in
                              FStar_Syntax_Subst.close uu____7678 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7677) in
                          FStar_Syntax_Syntax.Tm_let uu____7664 in
                        FStar_All.pipe_left mk1 uu____7663 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____7705 = is_rec || (is_app_pattern pat) in
            if uu____7705
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____7714 =
                let uu____7715 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7715 in
              mk1 uu____7714 in
            let uu____7716 =
              let uu____7717 =
                let uu____7740 =
                  let uu____7743 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7743
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7764 =
                  let uu____7779 =
                    let uu____7792 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7795 = desugar_term env t2 in
                    (uu____7792, FStar_Pervasives_Native.None, uu____7795) in
                  let uu____7804 =
                    let uu____7819 =
                      let uu____7832 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7835 = desugar_term env t3 in
                      (uu____7832, FStar_Pervasives_Native.None, uu____7835) in
                    [uu____7819] in
                  uu____7779 :: uu____7804 in
                (uu____7740, uu____7764) in
              FStar_Syntax_Syntax.Tm_match uu____7717 in
            mk1 uu____7716
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
            let desugar_branch uu____7976 =
              match uu____7976 with
              | (pat,wopt,b) ->
                  let uu____7994 = desugar_match_pat env pat in
                  (match uu____7994 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8015 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____8015 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____8017 =
              let uu____8018 =
                let uu____8041 = desugar_term env e in
                let uu____8042 = FStar_List.collect desugar_branch branches in
                (uu____8041, uu____8042) in
              FStar_Syntax_Syntax.Tm_match uu____8018 in
            FStar_All.pipe_left mk1 uu____8017
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8071 = is_comp_type env t in
              if uu____8071
              then
                let uu____8078 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8078
              else
                (let uu____8084 = desugar_term env t in
                 FStar_Util.Inl uu____8084) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8090 =
              let uu____8091 =
                let uu____8118 = desugar_term env e in
                (uu____8118, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8091 in
            FStar_All.pipe_left mk1 uu____8090
        | FStar_Parser_AST.Record (uu____8143,[]) ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8180 = FStar_List.hd fields in
              match uu____8180 with | (f,uu____8192) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8234  ->
                        match uu____8234 with
                        | (g,uu____8240) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8246,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8260 =
                         let uu____8261 =
                           let uu____8266 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8266, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8261 in
                       FStar_Exn.raise uu____8260
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
                  let uu____8274 =
                    let uu____8285 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8316  ->
                              match uu____8316 with
                              | (f,uu____8326) ->
                                  let uu____8327 =
                                    let uu____8328 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8328 in
                                  (uu____8327, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8285) in
                  FStar_Parser_AST.Construct uu____8274
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8346 =
                      let uu____8347 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8347 in
                    FStar_Parser_AST.mk_term uu____8346 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8349 =
                      let uu____8362 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8392  ->
                                match uu____8392 with
                                | (f,uu____8402) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8362) in
                    FStar_Parser_AST.Record uu____8349 in
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
                         FStar_Syntax_Syntax.pos = uu____8430;
                         FStar_Syntax_Syntax.vars = uu____8431;_},args);
                    FStar_Syntax_Syntax.pos = uu____8433;
                    FStar_Syntax_Syntax.vars = uu____8434;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8462 =
                     let uu____8463 =
                       let uu____8478 =
                         let uu____8479 =
                           let uu____8482 =
                             let uu____8483 =
                               let uu____8490 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8490) in
                             FStar_Syntax_Syntax.Record_ctor uu____8483 in
                           FStar_Pervasives_Native.Some uu____8482 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8479 in
                       (uu____8478, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8463 in
                   FStar_All.pipe_left mk1 uu____8462 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8521 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8525 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8525 with
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
                  let uu____8544 =
                    let uu____8545 =
                      let uu____8560 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8561 =
                        let uu____8564 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8564] in
                      (uu____8560, uu____8561) in
                    FStar_Syntax_Syntax.Tm_app uu____8545 in
                  FStar_All.pipe_left mk1 uu____8544))
        | FStar_Parser_AST.NamedTyp (uu____8569,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8572 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8573 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8574,uu____8575,uu____8576) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8589,uu____8590,uu____8591) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8604,uu____8605,uu____8606) ->
            failwith "Not implemented yet"
and not_ascribed: FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8620 -> false
    | uu____8629 -> true
and is_synth_by_tactic:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8635 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8635 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8639 -> false
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
           (fun uu____8676  ->
              match uu____8676 with
              | (a,imp) ->
                  let uu____8689 = desugar_term env a in
                  arg_withimp_e imp uu____8689))
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
        let is_requires uu____8708 =
          match uu____8708 with
          | (t1,uu____8714) ->
              let uu____8715 =
                let uu____8716 = unparen t1 in uu____8716.FStar_Parser_AST.tm in
              (match uu____8715 with
               | FStar_Parser_AST.Requires uu____8717 -> true
               | uu____8724 -> false) in
        let is_ensures uu____8732 =
          match uu____8732 with
          | (t1,uu____8738) ->
              let uu____8739 =
                let uu____8740 = unparen t1 in uu____8740.FStar_Parser_AST.tm in
              (match uu____8739 with
               | FStar_Parser_AST.Ensures uu____8741 -> true
               | uu____8748 -> false) in
        let is_app head1 uu____8759 =
          match uu____8759 with
          | (t1,uu____8765) ->
              let uu____8766 =
                let uu____8767 = unparen t1 in uu____8767.FStar_Parser_AST.tm in
              (match uu____8766 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8769;
                      FStar_Parser_AST.level = uu____8770;_},uu____8771,uu____8772)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____8773 -> false) in
        let is_smt_pat uu____8781 =
          match uu____8781 with
          | (t1,uu____8787) ->
              let uu____8788 =
                let uu____8789 = unparen t1 in uu____8789.FStar_Parser_AST.tm in
              (match uu____8788 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8792);
                             FStar_Parser_AST.range = uu____8793;
                             FStar_Parser_AST.level = uu____8794;_},uu____8795)::uu____8796::[])
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
                             FStar_Parser_AST.range = uu____8835;
                             FStar_Parser_AST.level = uu____8836;_},uu____8837)::uu____8838::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____8863 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8891 = head_and_args t1 in
          match uu____8891 with
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
                   let thunk_ens uu____8985 =
                     match uu____8985 with
                     | (e,i) ->
                         let uu____8996 = thunk_ens_ e in (uu____8996, i) in
                   let fail_lemma uu____9006 =
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
                         let uu____9086 =
                           let uu____9093 =
                             let uu____9100 = thunk_ens ens in
                             [uu____9100; nil_pat] in
                           req_true :: uu____9093 in
                         unit_tm :: uu____9086
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9147 =
                           let uu____9154 =
                             let uu____9161 = thunk_ens ens in
                             [uu____9161; nil_pat] in
                           req :: uu____9154 in
                         unit_tm :: uu____9147
                     | ens::smtpat::[] when
                         (((let uu____9210 = is_requires ens in
                            Prims.op_Negation uu____9210) &&
                             (let uu____9212 = is_smt_pat ens in
                              Prims.op_Negation uu____9212))
                            &&
                            (let uu____9214 = is_decreases ens in
                             Prims.op_Negation uu____9214))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9215 =
                           let uu____9222 =
                             let uu____9229 = thunk_ens ens in
                             [uu____9229; smtpat] in
                           req_true :: uu____9222 in
                         unit_tm :: uu____9215
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9276 =
                           let uu____9283 =
                             let uu____9290 = thunk_ens ens in
                             [uu____9290; nil_pat; dec] in
                           req_true :: uu____9283 in
                         unit_tm :: uu____9276
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9350 =
                           let uu____9357 =
                             let uu____9364 = thunk_ens ens in
                             [uu____9364; smtpat; dec] in
                           req_true :: uu____9357 in
                         unit_tm :: uu____9350
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9424 =
                           let uu____9431 =
                             let uu____9438 = thunk_ens ens in
                             [uu____9438; nil_pat; dec] in
                           req :: uu____9431 in
                         unit_tm :: uu____9424
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9498 =
                           let uu____9505 =
                             let uu____9512 = thunk_ens ens in
                             [uu____9512; smtpat] in
                           req :: uu____9505 in
                         unit_tm :: uu____9498
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9577 =
                           let uu____9584 =
                             let uu____9591 = thunk_ens ens in
                             [uu____9591; dec; smtpat] in
                           req :: uu____9584 in
                         unit_tm :: uu____9577
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9653 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9653, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9681 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9681
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9699 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9699
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
               | uu____9737 ->
                   let default_effect =
                     let uu____9739 = FStar_Options.ml_ish () in
                     if uu____9739
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9742 =
                           FStar_Options.warn_default_effects () in
                         if uu____9742
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9766 = pre_process_comp_typ t in
        match uu____9766 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9815 =
                  let uu____9816 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9816 in
                fail uu____9815)
             else ();
             (let is_universe uu____9825 =
                match uu____9825 with
                | (uu____9830,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9832 = FStar_Util.take is_universe args in
              match uu____9832 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9891  ->
                         match uu____9891 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9898 =
                    let uu____9913 = FStar_List.hd args1 in
                    let uu____9922 = FStar_List.tl args1 in
                    (uu____9913, uu____9922) in
                  (match uu____9898 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9977 =
                         let is_decrease uu____10013 =
                           match uu____10013 with
                           | (t1,uu____10023) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10033;
                                       FStar_Syntax_Syntax.vars = uu____10034;_},uu____10035::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10066 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9977 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10180  ->
                                      match uu____10180 with
                                      | (t1,uu____10190) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10199,(arg,uu____10201)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10230 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10244 -> false in
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
                                           | uu____10392 -> pat in
                                         let uu____10393 =
                                           let uu____10404 =
                                             let uu____10415 =
                                               let uu____10424 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10424, aq) in
                                             [uu____10415] in
                                           ens :: uu____10404 in
                                         req :: uu____10393
                                     | uu____10465 -> rest2
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
        | uu____10487 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___263_10504 = t in
        {
          FStar_Syntax_Syntax.n = (uu___263_10504.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___263_10504.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___264_10538 = b in
             {
               FStar_Parser_AST.b = (uu___264_10538.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___264_10538.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___264_10538.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10597 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10597)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10610 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10610 with
             | (env1,a1) ->
                 let a2 =
                   let uu___265_10620 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___265_10620.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___265_10620.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10642 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10656 =
                     let uu____10659 =
                       let uu____10660 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10660] in
                     no_annot_abs uu____10659 body2 in
                   FStar_All.pipe_left setpos uu____10656 in
                 let uu____10665 =
                   let uu____10666 =
                     let uu____10681 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10682 =
                       let uu____10685 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10685] in
                     (uu____10681, uu____10682) in
                   FStar_Syntax_Syntax.Tm_app uu____10666 in
                 FStar_All.pipe_left mk1 uu____10665)
        | uu____10690 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____10762 = q (rest, pats, body) in
              let uu____10769 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10762 uu____10769
                FStar_Parser_AST.Formula in
            let uu____10770 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10770 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10779 -> failwith "impossible" in
      let uu____10782 =
        let uu____10783 = unparen f in uu____10783.FStar_Parser_AST.tm in
      match uu____10782 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10790,uu____10791) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10802,uu____10803) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10834 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10834
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10870 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10870
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____10913 -> desugar_term env f
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
      let uu____10918 =
        FStar_List.fold_left
          (fun uu____10954  ->
             fun b  ->
               match uu____10954 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___266_11006 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___266_11006.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___266_11006.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___266_11006.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11023 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____11023 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___267_11043 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___267_11043.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___267_11043.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11060 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10918 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____11147 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11147)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11152 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11152)
      | FStar_Parser_AST.TVariable x ->
          let uu____11156 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11156)
      | FStar_Parser_AST.NoName t ->
          let uu____11164 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11164)
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
               (fun uu___231_11200  ->
                  match uu___231_11200 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11201 -> false)) in
        let quals2 q =
          let uu____11212 =
            (let uu____11215 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11215) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11212
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11228 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11228;
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
            let uu____11264 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11294  ->
                        match uu____11294 with
                        | (x,uu____11302) ->
                            let uu____11303 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11303 with
                             | (field_name,uu____11311) ->
                                 let only_decl =
                                   ((let uu____11315 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11315)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11317 =
                                        let uu____11318 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11318.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11317) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11332 =
                                       FStar_List.filter
                                         (fun uu___232_11336  ->
                                            match uu___232_11336 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11337 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11332
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___233_11350  ->
                                             match uu___233_11350 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11351 -> false)) in
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
                                      let uu____11359 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11359
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11364 =
                                        let uu____11369 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11369 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11364;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11371 =
                                        let uu____11372 =
                                          let uu____11379 =
                                            let uu____11382 =
                                              let uu____11383 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11383
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11382] in
                                          ((false, [lb]), uu____11379) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11372 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11371;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11264 FStar_List.flatten
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
            (lid,uu____11430,t,uu____11432,n1,uu____11434) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11439 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11439 with
             | (formals,uu____11455) ->
                 (match formals with
                  | [] -> []
                  | uu____11478 ->
                      let filter_records uu___234_11490 =
                        match uu___234_11490 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11493,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11505 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11507 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11507 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11517 = FStar_Util.first_N n1 formals in
                      (match uu____11517 with
                       | (uu____11540,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11566 -> []
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
                    let uu____11624 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11624
                    then
                      let uu____11627 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11627
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11630 =
                      let uu____11635 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11635 in
                    let uu____11636 =
                      let uu____11639 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11639 in
                    let uu____11642 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11630;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11636;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11642
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
          let tycon_id uu___235_11691 =
            match uu___235_11691 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11693,uu____11694) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11704,uu____11705,uu____11706) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11716,uu____11717,uu____11718) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____11748,uu____11749,uu____11750) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11792) ->
                let uu____11793 =
                  let uu____11794 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11794 in
                FStar_Parser_AST.mk_term uu____11793 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11796 =
                  let uu____11797 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11797 in
                FStar_Parser_AST.mk_term uu____11796 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11799) ->
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
              | uu____11822 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11828 =
                     let uu____11829 =
                       let uu____11836 = binder_to_term b in
                       (out, uu____11836, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11829 in
                   FStar_Parser_AST.mk_term uu____11828
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___236_11846 =
            match uu___236_11846 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____11901  ->
                       match uu____11901 with
                       | (x,t,uu____11912) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____11918 =
                    let uu____11919 =
                      let uu____11920 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11920 in
                    FStar_Parser_AST.mk_term uu____11919
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11918 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11924 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11951  ->
                          match uu____11951 with
                          | (x,uu____11961,uu____11962) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____11924)
            | uu____12015 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___237_12046 =
            match uu___237_12046 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____12070 = typars_of_binders _env binders in
                (match uu____12070 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12116 =
                         let uu____12117 =
                           let uu____12118 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12118 in
                         FStar_Parser_AST.mk_term uu____12117
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12116 binders in
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
            | uu____12131 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12175 =
              FStar_List.fold_left
                (fun uu____12215  ->
                   fun uu____12216  ->
                     match (uu____12215, uu____12216) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12307 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12307 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12175 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12420 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12420
                | uu____12421 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12429 = desugar_abstract_tc quals env [] tc in
              (match uu____12429 with
               | (uu____12442,uu____12443,se,uu____12445) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12448,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12465 =
                                 let uu____12466 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12466 in
                               if uu____12465
                               then
                                 let uu____12467 =
                                   let uu____12468 =
                                     FStar_Syntax_Print.lid_to_string l in
                                   FStar_Util.format1
                                     "Adding an implicit 'assume new' qualifier on %s"
                                     uu____12468 in
                                 FStar_Errors.warn
                                   se.FStar_Syntax_Syntax.sigrng uu____12467
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12475 ->
                               let uu____12476 =
                                 let uu____12479 =
                                   let uu____12480 =
                                     let uu____12493 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12493) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12480 in
                                 FStar_Syntax_Syntax.mk uu____12479 in
                               uu____12476 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___268_12497 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___268_12497.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___268_12497.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___268_12497.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12500 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12503 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12503
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12518 = typars_of_binders env binders in
              (match uu____12518 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12554 =
                           FStar_Util.for_some
                             (fun uu___238_12556  ->
                                match uu___238_12556 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12557 -> false) quals in
                         if uu____12554
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12564 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___239_12568  ->
                               match uu___239_12568 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12569 -> false)) in
                     if uu____12564
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12578 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12578
                     then
                       let uu____12581 =
                         let uu____12588 =
                           let uu____12589 = unparen t in
                           uu____12589.FStar_Parser_AST.tm in
                         match uu____12588 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12610 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12640)::args_rev ->
                                   let uu____12652 =
                                     let uu____12653 = unparen last_arg in
                                     uu____12653.FStar_Parser_AST.tm in
                                   (match uu____12652 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12681 -> ([], args))
                               | uu____12690 -> ([], args) in
                             (match uu____12610 with
                              | (cattributes,args1) ->
                                  let uu____12729 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12729))
                         | uu____12740 -> (t, []) in
                       match uu____12581 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___240_12762  ->
                                     match uu___240_12762 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____12763 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____12774)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12798 = tycon_record_as_variant trec in
              (match uu____12798 with
               | (t,fs) ->
                   let uu____12815 =
                     let uu____12818 =
                       let uu____12819 =
                         let uu____12828 =
                           let uu____12831 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12831 in
                         (uu____12828, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12819 in
                     uu____12818 :: quals in
                   desugar_tycon env d uu____12815 [t])
          | uu____12836::uu____12837 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____12998 = et in
                match uu____12998 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13223 ->
                         let trec = tc in
                         let uu____13247 = tycon_record_as_variant trec in
                         (match uu____13247 with
                          | (t,fs) ->
                              let uu____13306 =
                                let uu____13309 =
                                  let uu____13310 =
                                    let uu____13319 =
                                      let uu____13322 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13322 in
                                    (uu____13319, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13310 in
                                uu____13309 :: quals1 in
                              collect_tcs uu____13306 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13409 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13409 with
                          | (env2,uu____13469,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13618 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13618 with
                          | (env2,uu____13678,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13803 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13850 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13850 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___242_14361  ->
                             match uu___242_14361 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14428,uu____14429);
                                    FStar_Syntax_Syntax.sigrng = uu____14430;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14431;
                                    FStar_Syntax_Syntax.sigmeta = uu____14432;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14433;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14494 =
                                     typars_of_binders env1 binders in
                                   match uu____14494 with
                                   | (env2,tpars1) ->
                                       let uu____14525 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14525 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14558 =
                                   let uu____14579 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14579) in
                                 [uu____14558]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14647);
                                    FStar_Syntax_Syntax.sigrng = uu____14648;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14650;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14651;_},constrs,tconstr,quals1)
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
                                 let uu____14747 = push_tparams env1 tpars in
                                 (match uu____14747 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14824  ->
                                             match uu____14824 with
                                             | (x,uu____14838) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14846 =
                                        let uu____14875 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____14989  ->
                                                  match uu____14989 with
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
                                                        let uu____15045 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____15045 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___241_15056
                                                                 ->
                                                                match uu___241_15056
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15068
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____15076 =
                                                        let uu____15097 =
                                                          let uu____15098 =
                                                            let uu____15099 =
                                                              let uu____15114
                                                                =
                                                                let uu____15117
                                                                  =
                                                                  let uu____15120
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15120 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15117 in
                                                              (name, univs1,
                                                                uu____15114,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15099 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15098;
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
                                                          uu____15097) in
                                                      (name, uu____15076))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14875 in
                                      (match uu____14846 with
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
                             | uu____15359 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15491  ->
                             match uu____15491 with
                             | (name_doc,uu____15519,uu____15520) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15600  ->
                             match uu____15600 with
                             | (uu____15621,uu____15622,se) -> se)) in
                   let uu____15652 =
                     let uu____15659 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15659 rng in
                   (match uu____15652 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____15725  ->
                                  match uu____15725 with
                                  | (uu____15748,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15799,tps,k,uu____15802,constrs)
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
                                  | uu____15821 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15838  ->
                                 match uu____15838 with
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
      let uu____15875 =
        FStar_List.fold_left
          (fun uu____15898  ->
             fun b  ->
               match uu____15898 with
               | (env1,binders1) ->
                   let uu____15918 = desugar_binder env1 b in
                   (match uu____15918 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15935 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15935 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15952 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____15875 with
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
                let uu____16070 = desugar_binders monad_env eff_binders in
                match uu____16070 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16091 =
                        let uu____16092 =
                          let uu____16099 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16099 in
                        FStar_List.length uu____16092 in
                      uu____16091 = (Prims.parse_int "1") in
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
                          (uu____16141,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16143,uu____16144,uu____16145),uu____16146)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16179 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16180 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16192 = name_of_eff_decl decl in
                           FStar_List.mem uu____16192 mandatory_members)
                        eff_decls in
                    (match uu____16180 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16209 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16238  ->
                                   fun decl  ->
                                     match uu____16238 with
                                     | (env2,out) ->
                                         let uu____16258 =
                                           desugar_decl env2 decl in
                                         (match uu____16258 with
                                          | (env3,ses) ->
                                              let uu____16271 =
                                                let uu____16274 =
                                                  FStar_List.hd ses in
                                                uu____16274 :: out in
                                              (env3, uu____16271)))
                                (env1, [])) in
                         (match uu____16209 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16342,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16345,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16346,
                                                                (def,uu____16348)::
                                                                (cps_type,uu____16350)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16351;
                                                             FStar_Parser_AST.level
                                                               = uu____16352;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16404 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16404 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16424 =
                                                   let uu____16425 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16426 =
                                                     let uu____16427 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16427 in
                                                   let uu____16432 =
                                                     let uu____16433 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16433 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16425;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16426;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16432
                                                   } in
                                                 (uu____16424, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16440,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16443,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16478 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16478 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16498 =
                                                   let uu____16499 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16500 =
                                                     let uu____16501 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16501 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16499;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16500;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16498, doc1))
                                        | uu____16508 ->
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
                                let uu____16538 =
                                  let uu____16539 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16539 in
                                ([], uu____16538) in
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
                                    let uu____16556 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16556) in
                                  let uu____16563 =
                                    let uu____16564 =
                                      let uu____16565 =
                                        let uu____16566 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16566 in
                                      let uu____16575 = lookup "return" in
                                      let uu____16576 = lookup "bind" in
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
                                          uu____16565;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16575;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16576;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16564 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16563;
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
                                       (fun uu___243_16580  ->
                                          match uu___243_16580 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16581 -> true
                                          | uu____16582 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16592 =
                                     let uu____16593 =
                                       let uu____16594 = lookup "return_wp" in
                                       let uu____16595 = lookup "bind_wp" in
                                       let uu____16596 =
                                         lookup "if_then_else" in
                                       let uu____16597 = lookup "ite_wp" in
                                       let uu____16598 = lookup "stronger" in
                                       let uu____16599 = lookup "close_wp" in
                                       let uu____16600 = lookup "assert_p" in
                                       let uu____16601 = lookup "assume_p" in
                                       let uu____16602 = lookup "null_wp" in
                                       let uu____16603 = lookup "trivial" in
                                       let uu____16604 =
                                         if rr
                                         then
                                           let uu____16605 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16605
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16621 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16623 =
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
                                           uu____16594;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16595;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16596;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16597;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16598;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16599;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16600;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16601;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16602;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16603;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16604;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16621;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16623;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16593 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16592;
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
                                        fun uu____16648  ->
                                          match uu____16648 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16662 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16662 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16664 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16664
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
                let uu____16695 = desugar_binders env1 eff_binders in
                match uu____16695 with
                | (env2,binders) ->
                    let uu____16714 =
                      let uu____16733 = head_and_args defn in
                      match uu____16733 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16778 ->
                                let uu____16779 =
                                  let uu____16780 =
                                    let uu____16785 =
                                      let uu____16786 =
                                        let uu____16787 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____16787 " not found" in
                                      Prims.strcat "Effect " uu____16786 in
                                    (uu____16785,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16780 in
                                FStar_Exn.raise uu____16779 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16789 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16819)::args_rev ->
                                let uu____16831 =
                                  let uu____16832 = unparen last_arg in
                                  uu____16832.FStar_Parser_AST.tm in
                                (match uu____16831 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16860 -> ([], args))
                            | uu____16869 -> ([], args) in
                          (match uu____16789 with
                           | (cattributes,args1) ->
                               let uu____16920 = desugar_args env2 args1 in
                               let uu____16929 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16920, uu____16929)) in
                    (match uu____16714 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____16988 =
                           match uu____16988 with
                           | (uu____17001,x) ->
                               let uu____17007 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____17007 with
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
                                      let uu____17033 =
                                        let uu____17034 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____17034 in
                                      ([], uu____17033)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____17039 =
                             let uu____17040 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____17040 in
                           let uu____17051 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17052 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17053 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17054 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17055 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____17056 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17057 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17058 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17059 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17060 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____17061 =
                             let uu____17062 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____17062 in
                           let uu____17073 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17074 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17075 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____17083 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____17084 =
                                    let uu____17085 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____17085 in
                                  let uu____17096 =
                                    let uu____17097 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____17097 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____17083;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____17084;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____17096
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____17039;
                             FStar_Syntax_Syntax.ret_wp = uu____17051;
                             FStar_Syntax_Syntax.bind_wp = uu____17052;
                             FStar_Syntax_Syntax.if_then_else = uu____17053;
                             FStar_Syntax_Syntax.ite_wp = uu____17054;
                             FStar_Syntax_Syntax.stronger = uu____17055;
                             FStar_Syntax_Syntax.close_wp = uu____17056;
                             FStar_Syntax_Syntax.assert_p = uu____17057;
                             FStar_Syntax_Syntax.assume_p = uu____17058;
                             FStar_Syntax_Syntax.null_wp = uu____17059;
                             FStar_Syntax_Syntax.trivial = uu____17060;
                             FStar_Syntax_Syntax.repr = uu____17061;
                             FStar_Syntax_Syntax.return_repr = uu____17073;
                             FStar_Syntax_Syntax.bind_repr = uu____17074;
                             FStar_Syntax_Syntax.actions = uu____17075
                           } in
                         let se =
                           let for_free =
                             let uu____17110 =
                               let uu____17111 =
                                 let uu____17118 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____17118 in
                               FStar_List.length uu____17111 in
                             uu____17110 = (Prims.parse_int "1") in
                           let uu____17147 =
                             let uu____17150 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____17150 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____17147;
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
                                       let uu____17170 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____17170 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____17172 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____17172
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
    let uu____17187 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____17187 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17238 ->
              let uu____17239 =
                let uu____17240 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17240 in
              Prims.strcat "\n  " uu____17239
          | uu____17241 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____17254  ->
               match uu____17254 with
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
          let uu____17272 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____17272
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____17274 =
          let uu____17283 = FStar_Syntax_Syntax.as_arg arg in [uu____17283] in
        FStar_Syntax_Util.mk_app fv uu____17274
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17290 = desugar_decl_noattrs env d in
      match uu____17290 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____17310 = mk_comment_attr d in uu____17310 :: attrs1 in
          let uu____17315 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___269_17321 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___269_17321.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___269_17321.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___269_17321.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___269_17321.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____17315)
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
      | FStar_Parser_AST.Fsdoc uu____17347 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17363 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17363, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17402  ->
                 match uu____17402 with | (x,uu____17410) -> x) tcs in
          let uu____17415 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17415 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17437;
                    FStar_Parser_AST.prange = uu____17438;_},uu____17439)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17448;
                    FStar_Parser_AST.prange = uu____17449;_},uu____17450)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17465;
                         FStar_Parser_AST.prange = uu____17466;_},uu____17467);
                    FStar_Parser_AST.prange = uu____17468;_},uu____17469)::[]
                   -> false
               | (p,uu____17485)::[] ->
                   let uu____17494 = is_app_pattern p in
                   Prims.op_Negation uu____17494
               | uu____17495 -> false) in
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
            let uu____17514 =
              let uu____17515 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17515.FStar_Syntax_Syntax.n in
            (match uu____17514 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17523) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17556::uu____17557 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17560 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___244_17573  ->
                               match uu___244_17573 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17576;
                                   FStar_Syntax_Syntax.lbunivs = uu____17577;
                                   FStar_Syntax_Syntax.lbtyp = uu____17578;
                                   FStar_Syntax_Syntax.lbeff = uu____17579;
                                   FStar_Syntax_Syntax.lbdef = uu____17580;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17588;
                                   FStar_Syntax_Syntax.lbtyp = uu____17589;
                                   FStar_Syntax_Syntax.lbeff = uu____17590;
                                   FStar_Syntax_Syntax.lbdef = uu____17591;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17601 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17615  ->
                             match uu____17615 with
                             | (uu____17620,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17601
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17632 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17632
                   then
                     let uu____17641 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___270_17655 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___271_17657 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___271_17657.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___271_17657.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___270_17655.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___270_17655.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___270_17655.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___270_17655.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17641)
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
             | uu____17689 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17695 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17714 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17695 with
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
                       let uu___272_17738 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___272_17738.FStar_Parser_AST.prange)
                       }
                   | uu____17739 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___273_17746 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___273_17746.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___273_17746.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___273_17746.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17778 id =
                   match uu____17778 with
                   | (env1,ses) ->
                       let main =
                         let uu____17799 =
                           let uu____17800 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17800 in
                         FStar_Parser_AST.mk_term uu____17799
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
                       let uu____17850 = desugar_decl env1 id_decl in
                       (match uu____17850 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17868 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17868 FStar_Util.set_elements in
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
            let uu____17899 = close_fun env t in desugar_term env uu____17899 in
          let quals1 =
            let uu____17903 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17903
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____17909 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17909;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17921 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____17921 with
           | (t,uu____17935) ->
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
            let uu____17969 =
              let uu____17976 = FStar_Syntax_Syntax.null_binder t in
              [uu____17976] in
            let uu____17977 =
              let uu____17980 =
                let uu____17981 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17981 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17980 in
            FStar_Syntax_Util.arrow uu____17969 uu____17977 in
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
            let uu____18043 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____18043 with
            | FStar_Pervasives_Native.None  ->
                let uu____18046 =
                  let uu____18047 =
                    let uu____18052 =
                      let uu____18053 =
                        let uu____18054 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____18054 " not found" in
                      Prims.strcat "Effect name " uu____18053 in
                    (uu____18052, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____18047 in
                FStar_Exn.raise uu____18046
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____18058 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18100 =
                  let uu____18109 =
                    let uu____18116 = desugar_term env t in ([], uu____18116) in
                  FStar_Pervasives_Native.Some uu____18109 in
                (uu____18100, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18149 =
                  let uu____18158 =
                    let uu____18165 = desugar_term env wp in
                    ([], uu____18165) in
                  FStar_Pervasives_Native.Some uu____18158 in
                let uu____18174 =
                  let uu____18183 =
                    let uu____18190 = desugar_term env t in ([], uu____18190) in
                  FStar_Pervasives_Native.Some uu____18183 in
                (uu____18149, uu____18174)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18216 =
                  let uu____18225 =
                    let uu____18232 = desugar_term env t in ([], uu____18232) in
                  FStar_Pervasives_Native.Some uu____18225 in
                (FStar_Pervasives_Native.None, uu____18216) in
          (match uu____18058 with
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
      let uu____18322 =
        FStar_List.fold_left
          (fun uu____18342  ->
             fun d  ->
               match uu____18342 with
               | (env1,sigelts) ->
                   let uu____18362 = desugar_decl env1 d in
                   (match uu____18362 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____18322 with
      | (env1,sigelts) ->
          let rec forward acc uu___246_18403 =
            match uu___246_18403 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18417,FStar_Syntax_Syntax.Sig_let uu____18418) ->
                     let uu____18431 =
                       let uu____18434 =
                         let uu___274_18435 = se2 in
                         let uu____18436 =
                           let uu____18439 =
                             FStar_List.filter
                               (fun uu___245_18453  ->
                                  match uu___245_18453 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18457;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18458;_},uu____18459);
                                      FStar_Syntax_Syntax.pos = uu____18460;
                                      FStar_Syntax_Syntax.vars = uu____18461;_}
                                      when
                                      let uu____18484 =
                                        let uu____18485 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____18485 in
                                      uu____18484 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18486 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____18439
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___274_18435.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___274_18435.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___274_18435.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___274_18435.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18436
                         } in
                       uu____18434 :: se1 :: acc in
                     forward uu____18431 sigelts1
                 | uu____18491 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____18499 = forward [] sigelts in (env1, uu____18499)
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
          | (FStar_Pervasives_Native.None ,uu____18553) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18557;
               FStar_Syntax_Syntax.exports = uu____18558;
               FStar_Syntax_Syntax.is_interface = uu____18559;_},FStar_Parser_AST.Module
             (current_lid,uu____18561)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18569) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18572 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18608 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18608, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18625 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18625, mname, decls, false) in
        match uu____18572 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18655 = desugar_decls env2 decls in
            (match uu____18655 with
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
          let uu____18713 =
            (FStar_Options.interactive ()) &&
              (let uu____18715 =
                 let uu____18716 =
                   let uu____18717 = FStar_Options.file_list () in
                   FStar_List.hd uu____18717 in
                 FStar_Util.get_file_extension uu____18716 in
               FStar_List.mem uu____18715 ["fsti"; "fsi"]) in
          if uu____18713 then as_interface m else m in
        let uu____18721 = desugar_modul_common curmod env m1 in
        match uu____18721 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18736 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18754 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18754 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18770 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18770
            then
              let uu____18771 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18771
            else ());
           (let uu____18773 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18773, modul)))
let ast_modul_to_modul:
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____18788 = desugar_modul env modul in
      match uu____18788 with | (env1,modul1) -> (modul1, env1)
let decls_to_sigelts:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____18816 = desugar_decls env decls in
      match uu____18816 with | (env1,sigelts) -> (sigelts, env1)
let partial_ast_modul_to_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____18856 = desugar_partial_modul modul env a_modul in
        match uu____18856 with | (env1,modul1) -> (modul1, env1)
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.module_inclusion_info ->
      Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun m  ->
    fun mii  ->
      fun en  ->
        let uu____18884 =
          FStar_ToSyntax_Env.prepare_module_or_interface false false en
            m.FStar_Syntax_Syntax.name mii in
        match uu____18884 with
        | (en1,pop_when_done) ->
            let en2 =
              let uu____18896 =
                FStar_ToSyntax_Env.set_current_module en1
                  m.FStar_Syntax_Syntax.name in
              FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18896
                m.FStar_Syntax_Syntax.exports in
            let env = FStar_ToSyntax_Env.finish en2 m in
            let uu____18898 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  m.FStar_Syntax_Syntax.name env
              else env in
            ((), uu____18898)