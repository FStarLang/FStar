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
  fun uu___300_58  ->
    match uu___300_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___301_76  ->
        match uu___301_76 with
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
  fun uu___302_83  ->
    match uu___302_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___303_92  ->
    match uu___303_92 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____95 -> FStar_Pervasives_Native.None
let arg_withimp_e:
  'Auu____99 .
    FStar_Parser_AST.imp ->
      'Auu____99 ->
        ('Auu____99,FStar_Syntax_Syntax.arg_qualifier
                      FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp))
let arg_withimp_t:
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
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____151 -> true
            | uu____156 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____161 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____166 in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____170 =
      let uu____171 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____171 in
    FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____179 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____179 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____185) ->
          let uu____198 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____198 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____204,uu____205) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____208,uu____209) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____214,t1) -> is_comp_type env t1
      | uu____216 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____226 =
          let uu____229 =
            let uu____230 =
              let uu____235 = FStar_Parser_AST.compile_op n1 s r in
              (uu____235, r) in
            FStar_Ident.mk_ident uu____230 in
          [uu____229] in
        FStar_All.pipe_right uu____226 FStar_Ident.lid_of_ids
let op_as_term:
  'Auu____243 .
    FStar_ToSyntax_Env.env ->
      Prims.int ->
        'Auu____243 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____271 =
              let uu____272 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None in
              FStar_All.pipe_right uu____272 FStar_Syntax_Syntax.fv_to_tm in
            FStar_Pervasives_Native.Some uu____271 in
          let fallback uu____278 =
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
                let uu____281 = FStar_Options.ml_ish () in
                if uu____281
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
            | uu____285 -> FStar_Pervasives_Native.None in
          let uu____286 =
            let uu____293 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange in
            FStar_ToSyntax_Env.try_lookup_lid env uu____293 in
          match uu____286 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____305 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____321 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____321
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____360 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____364 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____364 with | (env1,uu____376) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____379,term) ->
          let uu____381 = free_type_vars env term in (env, uu____381)
      | FStar_Parser_AST.TAnnotated (id,uu____387) ->
          let uu____388 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____388 with | (env1,uu____400) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____404 = free_type_vars env t in (env, uu____404)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____411 =
        let uu____412 = unparen t in uu____412.FStar_Parser_AST.tm in
      match uu____411 with
      | FStar_Parser_AST.Labeled uu____415 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____425 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____425 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____438 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____445 -> []
      | FStar_Parser_AST.Uvar uu____446 -> []
      | FStar_Parser_AST.Var uu____447 -> []
      | FStar_Parser_AST.Projector uu____448 -> []
      | FStar_Parser_AST.Discrim uu____453 -> []
      | FStar_Parser_AST.Name uu____454 -> []
      | FStar_Parser_AST.Assign (uu____455,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____458) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____464) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____469,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____485,ts) ->
          FStar_List.collect
            (fun uu____506  ->
               match uu____506 with | (t1,uu____514) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____515,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____523) ->
          let uu____524 = free_type_vars env t1 in
          let uu____527 = free_type_vars env t2 in
          FStar_List.append uu____524 uu____527
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____532 = free_type_vars_b env b in
          (match uu____532 with
           | (env1,f) ->
               let uu____547 = free_type_vars env1 t1 in
               FStar_List.append f uu____547)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____556 =
            FStar_List.fold_left
              (fun uu____576  ->
                 fun binder  ->
                   match uu____576 with
                   | (env1,free) ->
                       let uu____596 = free_type_vars_b env1 binder in
                       (match uu____596 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____556 with
           | (env1,free) ->
               let uu____627 = free_type_vars env1 body in
               FStar_List.append free uu____627)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____636 =
            FStar_List.fold_left
              (fun uu____656  ->
                 fun binder  ->
                   match uu____656 with
                   | (env1,free) ->
                       let uu____676 = free_type_vars_b env1 binder in
                       (match uu____676 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____636 with
           | (env1,free) ->
               let uu____707 = free_type_vars env1 body in
               FStar_List.append free uu____707)
      | FStar_Parser_AST.Project (t1,uu____711) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____715 -> []
      | FStar_Parser_AST.Let uu____722 -> []
      | FStar_Parser_AST.LetOpen uu____735 -> []
      | FStar_Parser_AST.If uu____740 -> []
      | FStar_Parser_AST.QForall uu____747 -> []
      | FStar_Parser_AST.QExists uu____760 -> []
      | FStar_Parser_AST.Record uu____773 -> []
      | FStar_Parser_AST.Match uu____786 -> []
      | FStar_Parser_AST.TryWith uu____801 -> []
      | FStar_Parser_AST.Bind uu____816 -> []
      | FStar_Parser_AST.Seq uu____823 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____870 =
        let uu____871 = unparen t1 in uu____871.FStar_Parser_AST.tm in
      match uu____870 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____913 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____933 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____933 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____951 =
                     let uu____952 =
                       let uu____957 = tm_type x.FStar_Ident.idRange in
                       (x, uu____957) in
                     FStar_Parser_AST.TAnnotated uu____952 in
                   FStar_Parser_AST.mk_binder uu____951 x.FStar_Ident.idRange
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
        let uu____970 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____970 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____988 =
                     let uu____989 =
                       let uu____994 = tm_type x.FStar_Ident.idRange in
                       (x, uu____994) in
                     FStar_Parser_AST.TAnnotated uu____989 in
                   FStar_Parser_AST.mk_binder uu____988 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____996 =
             let uu____997 = unparen t in uu____997.FStar_Parser_AST.tm in
           match uu____996 with
           | FStar_Parser_AST.Product uu____998 -> t
           | uu____1005 ->
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
      | uu____1037 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1043,uu____1044) -> true
    | FStar_Parser_AST.PatVar (uu____1049,uu____1050) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1056) -> is_var_pattern p1
    | uu____1057 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1062) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1063;
           FStar_Parser_AST.prange = uu____1064;_},uu____1065)
        -> true
    | uu____1076 -> false
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
    | uu____1080 -> p
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
            let uu____1120 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1120 with
             | (name,args,uu____1151) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1177);
               FStar_Parser_AST.prange = uu____1178;_},args)
            when is_top_level1 ->
            let uu____1188 =
              let uu____1193 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____1193 in
            (uu____1188, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1203);
               FStar_Parser_AST.prange = uu____1204;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1222 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____1260 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1261,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1264 -> acc
      | FStar_Parser_AST.PatTvar uu____1265 -> acc
      | FStar_Parser_AST.PatOp uu____1272 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1280) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1289) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1304 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1304
      | FStar_Parser_AST.PatAscribed (pat,uu____1312) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1350 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1378 -> false
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
  fun uu___304_1404  ->
    match uu___304_1404 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1411 -> failwith "Impossible"
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
      fun uu___305_1436  ->
        match uu___305_1436 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1452 = FStar_Syntax_Syntax.null_binder k in
            (uu____1452, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1457 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1457 with
             | (env1,a1) ->
                 (((let uu___329_1477 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___329_1477.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___329_1477.FStar_Syntax_Syntax.index);
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
  fun uu____1496  ->
    match uu____1496 with
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
      let uu____1546 =
        let uu____1561 =
          let uu____1562 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1562 in
        let uu____1563 =
          let uu____1572 =
            let uu____1579 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1579) in
          [uu____1572] in
        (uu____1561, uu____1563) in
      FStar_Syntax_Syntax.Tm_app uu____1546 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1612 =
        let uu____1627 =
          let uu____1628 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1628 in
        let uu____1629 =
          let uu____1638 =
            let uu____1645 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1645) in
          [uu____1638] in
        (uu____1627, uu____1629) in
      FStar_Syntax_Syntax.Tm_app uu____1612 in
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
          let uu____1688 =
            let uu____1703 =
              let uu____1704 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____1704 in
            let uu____1705 =
              let uu____1714 =
                let uu____1721 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____1721) in
              let uu____1724 =
                let uu____1733 =
                  let uu____1740 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____1740) in
                [uu____1733] in
              uu____1714 :: uu____1724 in
            (uu____1703, uu____1705) in
          FStar_Syntax_Syntax.Tm_app uu____1688 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___306_1771  ->
    match uu___306_1771 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1772 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1780 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1780)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1795 =
      let uu____1796 = unparen t in uu____1796.FStar_Parser_AST.tm in
    match uu____1795 with
    | FStar_Parser_AST.Wild  ->
        let uu____1801 =
          let uu____1802 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1802 in
        FStar_Util.Inr uu____1801
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1813)) ->
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
             let uu____1879 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1879
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1890 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1890
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1901 =
               let uu____1902 =
                 let uu____1907 =
                   let uu____1908 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1908 in
                 (uu____1907, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1902 in
             FStar_Exn.raise uu____1901)
    | FStar_Parser_AST.App uu____1913 ->
        let rec aux t1 univargs =
          let uu____1943 =
            let uu____1944 = unparen t1 in uu____1944.FStar_Parser_AST.tm in
          match uu____1943 with
          | FStar_Parser_AST.App (t2,targ,uu____1951) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___307_1975  ->
                     match uu___307_1975 with
                     | FStar_Util.Inr uu____1980 -> true
                     | uu____1981 -> false) univargs
              then
                let uu____1986 =
                  let uu____1987 =
                    FStar_List.map
                      (fun uu___308_1996  ->
                         match uu___308_1996 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1987 in
                FStar_Util.Inr uu____1986
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___309_2013  ->
                        match uu___309_2013 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2019 -> failwith "impossible")
                     univargs in
                 let uu____2020 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2020)
          | uu____2026 ->
              let uu____2027 =
                let uu____2028 =
                  let uu____2033 =
                    let uu____2034 =
                      let uu____2035 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____2035 " in universe context" in
                    Prims.strcat "Unexpected term " uu____2034 in
                  (uu____2033, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____2028 in
              FStar_Exn.raise uu____2027 in
        aux t []
    | uu____2044 ->
        let uu____2045 =
          let uu____2046 =
            let uu____2051 =
              let uu____2052 =
                let uu____2053 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____2053 " in universe context" in
              Prims.strcat "Unexpected term " uu____2052 in
            (uu____2051, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____2046 in
        FStar_Exn.raise uu____2045
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields:
  'Auu____2072 .
    FStar_ToSyntax_Env.env ->
      (FStar_Ident.lident,'Auu____2072) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_ToSyntax_Env.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2097 = FStar_List.hd fields in
        match uu____2097 with
        | (f,uu____2107) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
              let check_field uu____2117 =
                match uu____2117 with
                | (f',uu____2123) ->
                    (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
                     (let uu____2125 =
                        FStar_ToSyntax_Env.belongs_to_record env f' record in
                      if uu____2125
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                             f'.FStar_Ident.str in
                         FStar_Exn.raise (FStar_Errors.Error (msg, rg))))) in
              (let uu____2129 = FStar_List.tl fields in
               FStar_List.iter check_field uu____2129);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2346 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2353 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2354 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2356,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2397  ->
                          match uu____2397 with
                          | (p3,uu____2407) ->
                              let uu____2408 =
                                let uu____2409 =
                                  let uu____2412 = pat_vars p3 in
                                  FStar_Util.set_intersect uu____2412 out in
                                FStar_Util.set_is_empty uu____2409 in
                              if uu____2408
                              then
                                let uu____2417 = pat_vars p3 in
                                FStar_Util.set_union out uu____2417
                              else
                                FStar_Exn.raise
                                  (FStar_Errors.Error
                                     ("Non-linear patterns are not permitted.",
                                       r))) FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2424) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2425) -> ()
         | (true ,uu____2432) ->
             FStar_Exn.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____2467 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2467 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2481 ->
               let uu____2484 = push_bv_maybe_mut e x in
               (match uu____2484 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           let orig = p1 in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2571 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2587 =
                 let uu____2588 =
                   let uu____2589 =
                     let uu____2596 =
                       let uu____2597 =
                         let uu____2602 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2602, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2597 in
                     (uu____2596, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2589 in
                 {
                   FStar_Parser_AST.pat = uu____2588;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2587
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2607 = aux loc env1 p2 in
               (match uu____2607 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___330_2661 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___331_2666 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___331_2666.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___331_2666.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___330_2661.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___332_2668 = p4 in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___333_2673 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___333_2673.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___333_2673.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___332_2668.FStar_Syntax_Syntax.p)
                          }
                      | uu____2674 when top -> p4
                      | uu____2675 ->
                          FStar_Exn.raise
                            (FStar_Errors.Error
                               ("Type ascriptions within patterns are only allowed on variables",
                                 (orig.FStar_Parser_AST.prange))) in
                    let uu____2678 =
                      match binder with
                      | LetBinder uu____2691 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2705 = close_fun env1 t in
                            desugar_term env1 uu____2705 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2707 -> true)
                           then
                             (let uu____2708 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2709 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2710 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                uu____2708 uu____2709 uu____2710)
                           else ();
                           (let uu____2712 = annot_pat_var p3 t1 in
                            (uu____2712,
                              (LocalBinder
                                 ((let uu___334_2718 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___334_2718.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___334_2718.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq))))) in
                    (match uu____2678 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2740 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2740, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2751 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2751, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2772 = resolvex loc env1 x in
               (match uu____2772 with
                | (loc1,env2,xbv) ->
                    let uu____2794 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2794, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2815 = resolvex loc env1 x in
               (match uu____2815 with
                | (loc1,env2,xbv) ->
                    let uu____2837 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2837, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2849 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2849, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2873;_},args)
               ->
               let uu____2879 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2920  ->
                        match uu____2920 with
                        | (loc1,env2,args1) ->
                            let uu____2968 = aux loc1 env2 arg in
                            (match uu____2968 with
                             | (loc2,env3,uu____2997,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2879 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3067 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3067, false))
           | FStar_Parser_AST.PatApp uu____3084 ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3106 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3139  ->
                        match uu____3139 with
                        | (loc1,env2,pats1) ->
                            let uu____3171 = aux loc1 env2 pat in
                            (match uu____3171 with
                             | (loc2,env3,uu____3196,pat1,uu____3198) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3106 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3241 =
                        let uu____3244 =
                          let uu____3249 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3249 in
                        let uu____3250 =
                          let uu____3251 =
                            let uu____3264 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3264, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3251 in
                        FStar_All.pipe_left uu____3244 uu____3250 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3296 =
                               let uu____3297 =
                                 let uu____3310 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3310, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3297 in
                             FStar_All.pipe_left (pos_r r) uu____3296) pats1
                        uu____3241 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3354 =
                 FStar_List.fold_left
                   (fun uu____3394  ->
                      fun p2  ->
                        match uu____3394 with
                        | (loc1,env2,pats) ->
                            let uu____3443 = aux loc1 env2 p2 in
                            (match uu____3443 with
                             | (loc2,env3,uu____3472,pat,uu____3474) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3354 with
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
                    let uu____3569 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3569 with
                     | (constr,uu____3591) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3594 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3596 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3596, false)))
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
                      (fun uu____3667  ->
                         match uu____3667 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3697  ->
                         match uu____3697 with
                         | (f,uu____3703) ->
                             let uu____3704 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3730  ->
                                       match uu____3730 with
                                       | (g,uu____3736) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3704 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3741,p2)
                                  -> p2))) in
               let app =
                 let uu____3748 =
                   let uu____3749 =
                     let uu____3756 =
                       let uu____3757 =
                         let uu____3758 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3758 in
                       FStar_Parser_AST.mk_pattern uu____3757
                         p1.FStar_Parser_AST.prange in
                     (uu____3756, args) in
                   FStar_Parser_AST.PatApp uu____3749 in
                 FStar_Parser_AST.mk_pattern uu____3748
                   p1.FStar_Parser_AST.prange in
               let uu____3761 = aux loc env1 app in
               (match uu____3761 with
                | (env2,e,b,p2,uu____3790) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3818 =
                            let uu____3819 =
                              let uu____3832 =
                                let uu___335_3833 = fv in
                                let uu____3834 =
                                  let uu____3837 =
                                    let uu____3838 =
                                      let uu____3845 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3845) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3838 in
                                  FStar_Pervasives_Native.Some uu____3837 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___335_3833.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___335_3833.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3834
                                } in
                              (uu____3832, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3819 in
                          FStar_All.pipe_left pos uu____3818
                      | uu____3872 -> p2 in
                    (env2, e, b, p3, false))
         and aux loc env1 p1 = aux' false loc env1 p1 in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3922 = aux' true loc env1 p2 in
               (match uu____3922 with
                | (loc1,env2,var,p3,uu____3949) ->
                    let uu____3954 =
                      FStar_List.fold_left
                        (fun uu____3986  ->
                           fun p4  ->
                             match uu____3986 with
                             | (loc2,env3,ps1) ->
                                 let uu____4019 = aux' true loc2 env3 p4 in
                                 (match uu____4019 with
                                  | (loc3,env4,uu____4044,p5,uu____4046) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____3954 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4097 ->
               let uu____4098 = aux' true loc env1 p1 in
               (match uu____4098 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4138 = aux_maybe_or env p in
         match uu____4138 with
         | (env1,b,pats) ->
             ((let uu____4169 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4169);
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
            let uu____4206 =
              let uu____4207 =
                let uu____4212 = FStar_ToSyntax_Env.qualify env x in
                (uu____4212, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4207 in
            (env, uu____4206, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4232 =
                  let uu____4233 =
                    let uu____4238 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4238, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4233 in
                mklet uu____4232
            | FStar_Parser_AST.PatVar (x,uu____4240) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4246);
                   FStar_Parser_AST.prange = uu____4247;_},t)
                ->
                let uu____4253 =
                  let uu____4254 =
                    let uu____4259 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4260 = desugar_term env t in
                    (uu____4259, uu____4260) in
                  LetBinder uu____4254 in
                (env, uu____4253, [])
            | uu____4263 ->
                FStar_Exn.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4273 = desugar_data_pat env p is_mut in
             match uu____4273 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4302;
                       FStar_Syntax_Syntax.p = uu____4303;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4308;
                       FStar_Syntax_Syntax.p = uu____4309;_}::[] -> []
                   | uu____4314 -> p1 in
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
  fun uu____4321  ->
    fun env  ->
      fun pat  ->
        let uu____4324 = desugar_data_pat env pat false in
        match uu____4324 with | (env1,uu____4340,pat1) -> (env1, pat1)
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
      fun uu____4358  ->
        fun range  ->
          match uu____4358 with
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
                         | FStar_Const.Int64  -> "64"))) in
              ((let uu____4368 =
                  let uu____4369 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____4369 in
                if uu____4368
                then
                  let uu____4370 =
                    let uu____4371 =
                      let uu____4376 =
                        FStar_Util.format2
                          "%s is not in the expected range for %s" repr tnm in
                      (uu____4376, range) in
                    FStar_Errors.Error uu____4371 in
                  FStar_Exn.raise uu____4370
                else ());
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
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range in
                let lid1 =
                  let uu____4384 = FStar_ToSyntax_Env.try_lookup_lid env lid in
                  match uu____4384 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4394) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range in
                           let private_fv =
                             let uu____4404 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4404 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___336_4405 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___336_4405.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___336_4405.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4406 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4413 =
                        let uu____4414 =
                          let uu____4419 =
                            FStar_Util.format1
                              "Unexpected numeric literal.  Restart F* to load %s."
                              tnm in
                          (uu____4419, range) in
                        FStar_Errors.Error uu____4414 in
                      FStar_Exn.raise uu____4413 in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range in
                let uu____4435 =
                  let uu____4438 =
                    let uu____4439 =
                      let uu____4454 =
                        let uu____4463 =
                          let uu____4470 =
                            FStar_Syntax_Syntax.as_implicit false in
                          (repr1, uu____4470) in
                        [uu____4463] in
                      (lid1, uu____4454) in
                    FStar_Syntax_Syntax.Tm_app uu____4439 in
                  FStar_Syntax_Syntax.mk uu____4438 in
                uu____4435 FStar_Pervasives_Native.None range))
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
            let uu____4509 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4509 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4524 =
                    let uu____4525 =
                      let uu____4532 = mk_ref_read tm1 in
                      (uu____4532,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4525 in
                  FStar_All.pipe_left mk1 uu____4524
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4548 =
          let uu____4549 = unparen t in uu____4549.FStar_Parser_AST.tm in
        match uu____4548 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4550; FStar_Ident.ident = uu____4551;
              FStar_Ident.nsstr = uu____4552; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4555 ->
            let uu____4556 =
              let uu____4557 =
                let uu____4562 =
                  let uu____4563 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4563 in
                (uu____4562, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4557 in
            FStar_Exn.raise uu____4556 in
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
          let uu___337_4583 = e in
          {
            FStar_Syntax_Syntax.n = (uu___337_4583.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___337_4583.FStar_Syntax_Syntax.vars)
          } in
        let uu____4586 =
          let uu____4587 = unparen top in uu____4587.FStar_Parser_AST.tm in
        match uu____4586 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4588 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4639::uu____4640::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4644 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4644 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4657;_},t1::t2::[])
                  ->
                  let uu____4662 = flatten1 t1 in
                  FStar_List.append uu____4662 [t2]
              | uu____4665 -> [t] in
            let targs =
              let uu____4669 =
                let uu____4672 = unparen top in flatten1 uu____4672 in
              FStar_All.pipe_right uu____4669
                (FStar_List.map
                   (fun t  ->
                      let uu____4680 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4680)) in
            let uu____4681 =
              let uu____4686 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4686 in
            (match uu____4681 with
             | (tup,uu____4692) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4696 =
              let uu____4699 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4699 in
            FStar_All.pipe_left setpos uu____4696
        | FStar_Parser_AST.Uvar u ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4719 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____4719 with
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
                             let uu____4751 = desugar_term env t in
                             (uu____4751, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4765)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4780 =
              let uu___338_4781 = top in
              let uu____4782 =
                let uu____4783 =
                  let uu____4790 =
                    let uu___339_4791 = top in
                    let uu____4792 =
                      let uu____4793 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4793 in
                    {
                      FStar_Parser_AST.tm = uu____4792;
                      FStar_Parser_AST.range =
                        (uu___339_4791.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___339_4791.FStar_Parser_AST.level)
                    } in
                  (uu____4790, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4783 in
              {
                FStar_Parser_AST.tm = uu____4782;
                FStar_Parser_AST.range =
                  (uu___338_4781.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___338_4781.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4780
        | FStar_Parser_AST.Construct (n1,(a,uu____4796)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.warn top.FStar_Parser_AST.range
               "SMTPatT is deprecated; please just use SMTPat";
             (let uu____4812 =
                let uu___340_4813 = top in
                let uu____4814 =
                  let uu____4815 =
                    let uu____4822 =
                      let uu___341_4823 = top in
                      let uu____4824 =
                        let uu____4825 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____4825 in
                      {
                        FStar_Parser_AST.tm = uu____4824;
                        FStar_Parser_AST.range =
                          (uu___341_4823.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___341_4823.FStar_Parser_AST.level)
                      } in
                    (uu____4822, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____4815 in
                {
                  FStar_Parser_AST.tm = uu____4814;
                  FStar_Parser_AST.range =
                    (uu___340_4813.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___340_4813.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____4812))
        | FStar_Parser_AST.Construct (n1,(a,uu____4828)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4843 =
              let uu___342_4844 = top in
              let uu____4845 =
                let uu____4846 =
                  let uu____4853 =
                    let uu___343_4854 = top in
                    let uu____4855 =
                      let uu____4856 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4856 in
                    {
                      FStar_Parser_AST.tm = uu____4855;
                      FStar_Parser_AST.range =
                        (uu___343_4854.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___343_4854.FStar_Parser_AST.level)
                    } in
                  (uu____4853, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4846 in
              {
                FStar_Parser_AST.tm = uu____4845;
                FStar_Parser_AST.range =
                  (uu___342_4844.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___342_4844.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4843
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4857; FStar_Ident.ident = uu____4858;
              FStar_Ident.nsstr = uu____4859; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4862; FStar_Ident.ident = uu____4863;
              FStar_Ident.nsstr = uu____4864; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4867; FStar_Ident.ident = uu____4868;
               FStar_Ident.nsstr = uu____4869; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____4887 =
              let uu____4888 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____4888 in
            mk1 uu____4887
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4889; FStar_Ident.ident = uu____4890;
              FStar_Ident.nsstr = uu____4891; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4894; FStar_Ident.ident = uu____4895;
              FStar_Ident.nsstr = uu____4896; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4899; FStar_Ident.ident = uu____4900;
              FStar_Ident.nsstr = uu____4901; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____4906;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____4908 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____4908 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____4913 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____4913))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____4917 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____4917 with
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
                let uu____4944 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____4944 with
                | FStar_Pervasives_Native.Some uu____4953 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____4958 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____4958 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____4972 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____4985 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____4985
              | uu____4986 ->
                  let uu____4993 =
                    let uu____4994 =
                      let uu____4999 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____4999, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____4994 in
                  FStar_Exn.raise uu____4993))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5002 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5002 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5005 =
                    let uu____5006 =
                      let uu____5011 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5011, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5006 in
                  FStar_Exn.raise uu____5005
              | uu____5012 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5031 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5031 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5035 =
                    let uu____5042 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5042, true) in
                  (match uu____5035 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5057 ->
                            let uu____5064 =
                              FStar_Util.take
                                (fun uu____5088  ->
                                   match uu____5088 with
                                   | (uu____5093,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5064 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5157  ->
                                        match uu____5157 with
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
                    let uu____5200 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5200 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5203 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  FStar_Exn.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5210 =
              FStar_List.fold_left
                (fun uu____5255  ->
                   fun b  ->
                     match uu____5255 with
                     | (env1,tparams,typs) ->
                         let uu____5312 = desugar_binder env1 b in
                         (match uu____5312 with
                          | (xopt,t1) ->
                              let uu____5341 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5350 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5350)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5341 with
                               | (env2,x) ->
                                   let uu____5370 =
                                     let uu____5373 =
                                       let uu____5376 =
                                         let uu____5377 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5377 in
                                       [uu____5376] in
                                     FStar_List.append typs uu____5373 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___344_5403 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___344_5403.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___344_5403.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5370)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5210 with
             | (env1,uu____5427,targs) ->
                 let uu____5449 =
                   let uu____5454 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5454 in
                 (match uu____5449 with
                  | (tup,uu____5460) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5471 = uncurry binders t in
            (match uu____5471 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___310_5503 =
                   match uu___310_5503 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5517 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5517
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5539 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5539 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5554 = desugar_binder env b in
            (match uu____5554 with
             | (FStar_Pervasives_Native.None ,uu____5561) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5571 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5571 with
                  | ((x,uu____5577),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5584 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5584))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5604 =
              FStar_List.fold_left
                (fun uu____5624  ->
                   fun pat  ->
                     match uu____5624 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5650,t) ->
                              let uu____5652 =
                                let uu____5655 = free_type_vars env1 t in
                                FStar_List.append uu____5655 ftvs in
                              (env1, uu____5652)
                          | uu____5660 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5604 with
             | (uu____5665,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5677 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5677 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___311_5718 =
                   match uu___311_5718 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5756 =
                                 let uu____5757 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5757
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5756 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____5810 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____5810
                   | p::rest ->
                       let uu____5821 = desugar_binding_pat env1 p in
                       (match uu____5821 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5845 ->
                                  FStar_Exn.raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____5850 =
                              match b with
                              | LetBinder uu____5883 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____5933) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____5969 =
                                          let uu____5974 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____5974, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____5969
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6010,uu____6011) ->
                                             let tup2 =
                                               let uu____6013 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6013
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6017 =
                                                 let uu____6020 =
                                                   let uu____6021 =
                                                     let uu____6036 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6039 =
                                                       let uu____6042 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6043 =
                                                         let uu____6046 =
                                                           let uu____6047 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6047 in
                                                         [uu____6046] in
                                                       uu____6042 ::
                                                         uu____6043 in
                                                     (uu____6036, uu____6039) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6021 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6020 in
                                               uu____6017
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6058 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6058 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6089,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6091,pats)) ->
                                             let tupn =
                                               let uu____6130 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6130
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6140 =
                                                 let uu____6141 =
                                                   let uu____6156 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6159 =
                                                     let uu____6168 =
                                                       let uu____6177 =
                                                         let uu____6178 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6178 in
                                                       [uu____6177] in
                                                     FStar_List.append args
                                                       uu____6168 in
                                                   (uu____6156, uu____6159) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6141 in
                                               mk1 uu____6140 in
                                             let p2 =
                                               let uu____6198 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6198 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6233 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____5850 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6300,uu____6301,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6315 =
                let uu____6316 = unparen e in uu____6316.FStar_Parser_AST.tm in
              match uu____6315 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6322 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6326 ->
            let rec aux args e =
              let uu____6358 =
                let uu____6359 = unparen e in uu____6359.FStar_Parser_AST.tm in
              match uu____6358 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6372 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6372 in
                  aux (arg :: args) e1
              | uu____6385 ->
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
              let uu____6411 =
                let uu____6412 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6412 in
              FStar_Parser_AST.mk_term uu____6411 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6413 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6413
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6416 =
              let uu____6417 =
                let uu____6424 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6424,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6417 in
            mk1 uu____6416
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6442 =
              let uu____6447 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6447 then desugar_typ else desugar_term in
            uu____6442 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6480 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6566  ->
                        match uu____6566 with
                        | (p,def) ->
                            let uu____6591 = is_app_pattern p in
                            if uu____6591
                            then
                              let uu____6610 =
                                destruct_app_pattern env top_level p in
                              (uu____6610, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6664 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____6664, def1)
                               | uu____6693 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____6719);
                                           FStar_Parser_AST.prange =
                                             uu____6720;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6744 =
                                            let uu____6759 =
                                              let uu____6764 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6764 in
                                            (uu____6759, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____6744, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____6811)
                                        ->
                                        if top_level
                                        then
                                          let uu____6834 =
                                            let uu____6849 =
                                              let uu____6854 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____6854 in
                                            (uu____6849, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____6834, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____6900 ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____6919 =
                FStar_List.fold_left
                  (fun uu____6979  ->
                     fun uu____6980  ->
                       match (uu____6979, uu____6980) with
                       | ((env1,fnames,rec_bindings),((f,uu____7063,uu____7064),uu____7065))
                           ->
                           let uu____7144 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7170 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7170 with
                                  | (env2,xx) ->
                                      let uu____7189 =
                                        let uu____7192 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7192 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7189))
                             | FStar_Util.Inr l ->
                                 let uu____7200 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7200, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7144 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____6919 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7326 =
                    match uu____7326 with
                    | ((uu____7349,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7393 = is_comp_type env1 t in
                                if uu____7393
                                then
                                  ((let uu____7395 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7405 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7405)) in
                                    match uu____7395 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Exn.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7408 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7410 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7410))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7408
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7414 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7414 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7418 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7433 =
                                let uu____7434 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7434
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7433 in
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
                  let uu____7468 =
                    let uu____7469 =
                      let uu____7482 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7482) in
                    FStar_Syntax_Syntax.Tm_let uu____7469 in
                  FStar_All.pipe_left mk1 uu____7468 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7513 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7513 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7540 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7540
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
                    | LocalBinder (x,uu____7552) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7555;
                              FStar_Syntax_Syntax.p = uu____7556;_}::[] ->
                              body1
                          | uu____7561 ->
                              let uu____7564 =
                                let uu____7567 =
                                  let uu____7568 =
                                    let uu____7591 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7592 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7591, uu____7592) in
                                  FStar_Syntax_Syntax.Tm_match uu____7568 in
                                FStar_Syntax_Syntax.mk uu____7567 in
                              uu____7564 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7602 =
                          let uu____7603 =
                            let uu____7616 =
                              let uu____7617 =
                                let uu____7618 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____7618] in
                              FStar_Syntax_Subst.close uu____7617 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____7616) in
                          FStar_Syntax_Syntax.Tm_let uu____7603 in
                        FStar_All.pipe_left mk1 uu____7602 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____7644 = is_rec || (is_app_pattern pat) in
            if uu____7644
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____7653 =
                let uu____7654 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____7654 in
              mk1 uu____7653 in
            let uu____7655 =
              let uu____7656 =
                let uu____7679 =
                  let uu____7682 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____7682
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____7703 =
                  let uu____7718 =
                    let uu____7731 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____7734 = desugar_term env t2 in
                    (uu____7731, FStar_Pervasives_Native.None, uu____7734) in
                  let uu____7743 =
                    let uu____7758 =
                      let uu____7771 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____7774 = desugar_term env t3 in
                      (uu____7771, FStar_Pervasives_Native.None, uu____7774) in
                    [uu____7758] in
                  uu____7718 :: uu____7743 in
                (uu____7679, uu____7703) in
              FStar_Syntax_Syntax.Tm_match uu____7656 in
            mk1 uu____7655
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
            let desugar_branch uu____7915 =
              match uu____7915 with
              | (pat,wopt,b) ->
                  let uu____7933 = desugar_match_pat env pat in
                  (match uu____7933 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____7954 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____7954 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____7956 =
              let uu____7957 =
                let uu____7980 = desugar_term env e in
                let uu____7981 = FStar_List.collect desugar_branch branches in
                (uu____7980, uu____7981) in
              FStar_Syntax_Syntax.Tm_match uu____7957 in
            FStar_All.pipe_left mk1 uu____7956
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8010 = is_comp_type env t in
              if uu____8010
              then
                let uu____8017 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8017
              else
                (let uu____8023 = desugar_term env t in
                 FStar_Util.Inl uu____8023) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8029 =
              let uu____8030 =
                let uu____8057 = desugar_term env e in
                (uu____8057, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8030 in
            FStar_All.pipe_left mk1 uu____8029
        | FStar_Parser_AST.Record (uu____8082,[]) ->
            FStar_Exn.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8119 = FStar_List.hd fields in
              match uu____8119 with | (f,uu____8131) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8173  ->
                        match uu____8173 with
                        | (g,uu____8179) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8185,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8199 =
                         let uu____8200 =
                           let uu____8205 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8205, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8200 in
                       FStar_Exn.raise uu____8199
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
                  let uu____8213 =
                    let uu____8224 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8255  ->
                              match uu____8255 with
                              | (f,uu____8265) ->
                                  let uu____8266 =
                                    let uu____8267 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8267 in
                                  (uu____8266, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8224) in
                  FStar_Parser_AST.Construct uu____8213
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8285 =
                      let uu____8286 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8286 in
                    FStar_Parser_AST.mk_term uu____8285 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8288 =
                      let uu____8301 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8331  ->
                                match uu____8331 with
                                | (f,uu____8341) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8301) in
                    FStar_Parser_AST.Record uu____8288 in
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
                         FStar_Syntax_Syntax.pos = uu____8369;
                         FStar_Syntax_Syntax.vars = uu____8370;_},args);
                    FStar_Syntax_Syntax.pos = uu____8372;
                    FStar_Syntax_Syntax.vars = uu____8373;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8401 =
                     let uu____8402 =
                       let uu____8417 =
                         let uu____8418 =
                           let uu____8421 =
                             let uu____8422 =
                               let uu____8429 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8429) in
                             FStar_Syntax_Syntax.Record_ctor uu____8422 in
                           FStar_Pervasives_Native.Some uu____8421 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8418 in
                       (uu____8417, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8402 in
                   FStar_All.pipe_left mk1 uu____8401 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8460 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8464 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8464 with
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
                  let uu____8483 =
                    let uu____8484 =
                      let uu____8499 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____8500 =
                        let uu____8503 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____8503] in
                      (uu____8499, uu____8500) in
                    FStar_Syntax_Syntax.Tm_app uu____8484 in
                  FStar_All.pipe_left mk1 uu____8483))
        | FStar_Parser_AST.NamedTyp (uu____8508,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____8511 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8512 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____8513,uu____8514,uu____8515) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____8528,uu____8529,uu____8530) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____8543,uu____8544,uu____8545) ->
            failwith "Not implemented yet"
and not_ascribed: FStar_Parser_AST.term -> Prims.bool =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8559 -> false
    | uu____8568 -> true
and is_synth_by_tactic:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____8574 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid in
          (match uu____8574 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____8578 -> false
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
           (fun uu____8615  ->
              match uu____8615 with
              | (a,imp) ->
                  let uu____8628 = desugar_term env a in
                  arg_withimp_e imp uu____8628))
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
        let is_requires uu____8647 =
          match uu____8647 with
          | (t1,uu____8653) ->
              let uu____8654 =
                let uu____8655 = unparen t1 in uu____8655.FStar_Parser_AST.tm in
              (match uu____8654 with
               | FStar_Parser_AST.Requires uu____8656 -> true
               | uu____8663 -> false) in
        let is_ensures uu____8671 =
          match uu____8671 with
          | (t1,uu____8677) ->
              let uu____8678 =
                let uu____8679 = unparen t1 in uu____8679.FStar_Parser_AST.tm in
              (match uu____8678 with
               | FStar_Parser_AST.Ensures uu____8680 -> true
               | uu____8687 -> false) in
        let is_app head1 uu____8698 =
          match uu____8698 with
          | (t1,uu____8704) ->
              let uu____8705 =
                let uu____8706 = unparen t1 in uu____8706.FStar_Parser_AST.tm in
              (match uu____8705 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____8708;
                      FStar_Parser_AST.level = uu____8709;_},uu____8710,uu____8711)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____8712 -> false) in
        let is_smt_pat uu____8720 =
          match uu____8720 with
          | (t1,uu____8726) ->
              let uu____8727 =
                let uu____8728 = unparen t1 in uu____8728.FStar_Parser_AST.tm in
              (match uu____8727 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____8731);
                             FStar_Parser_AST.range = uu____8732;
                             FStar_Parser_AST.level = uu____8733;_},uu____8734)::uu____8735::[])
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
                             FStar_Parser_AST.range = uu____8774;
                             FStar_Parser_AST.level = uu____8775;_},uu____8776)::uu____8777::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____8802 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____8830 = head_and_args t1 in
          match uu____8830 with
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
                   let thunk_ens uu____8924 =
                     match uu____8924 with
                     | (e,i) ->
                         let uu____8935 = thunk_ens_ e in (uu____8935, i) in
                   let fail_lemma uu____8945 =
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
                         let uu____9025 =
                           let uu____9032 =
                             let uu____9039 = thunk_ens ens in
                             [uu____9039; nil_pat] in
                           req_true :: uu____9032 in
                         unit_tm :: uu____9025
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9086 =
                           let uu____9093 =
                             let uu____9100 = thunk_ens ens in
                             [uu____9100; nil_pat] in
                           req :: uu____9093 in
                         unit_tm :: uu____9086
                     | ens::smtpat::[] when
                         (((let uu____9149 = is_requires ens in
                            Prims.op_Negation uu____9149) &&
                             (let uu____9151 = is_smt_pat ens in
                              Prims.op_Negation uu____9151))
                            &&
                            (let uu____9153 = is_decreases ens in
                             Prims.op_Negation uu____9153))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9154 =
                           let uu____9161 =
                             let uu____9168 = thunk_ens ens in
                             [uu____9168; smtpat] in
                           req_true :: uu____9161 in
                         unit_tm :: uu____9154
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9215 =
                           let uu____9222 =
                             let uu____9229 = thunk_ens ens in
                             [uu____9229; nil_pat; dec] in
                           req_true :: uu____9222 in
                         unit_tm :: uu____9215
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9289 =
                           let uu____9296 =
                             let uu____9303 = thunk_ens ens in
                             [uu____9303; smtpat; dec] in
                           req_true :: uu____9296 in
                         unit_tm :: uu____9289
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9363 =
                           let uu____9370 =
                             let uu____9377 = thunk_ens ens in
                             [uu____9377; nil_pat; dec] in
                           req :: uu____9370 in
                         unit_tm :: uu____9363
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9437 =
                           let uu____9444 =
                             let uu____9451 = thunk_ens ens in
                             [uu____9451; smtpat] in
                           req :: uu____9444 in
                         unit_tm :: uu____9437
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9516 =
                           let uu____9523 =
                             let uu____9530 = thunk_ens ens in
                             [uu____9530; dec; smtpat] in
                           req :: uu____9523 in
                         unit_tm :: uu____9516
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9592 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9592, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9620 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9620
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9638 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9638
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
               | uu____9676 ->
                   let default_effect =
                     let uu____9678 = FStar_Options.ml_ish () in
                     if uu____9678
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9681 =
                           FStar_Options.warn_default_effects () in
                         if uu____9681
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9705 = pre_process_comp_typ t in
        match uu____9705 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9754 =
                  let uu____9755 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9755 in
                fail uu____9754)
             else ();
             (let is_universe uu____9764 =
                match uu____9764 with
                | (uu____9769,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9771 = FStar_Util.take is_universe args in
              match uu____9771 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9830  ->
                         match uu____9830 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9837 =
                    let uu____9852 = FStar_List.hd args1 in
                    let uu____9861 = FStar_List.tl args1 in
                    (uu____9852, uu____9861) in
                  (match uu____9837 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____9916 =
                         let is_decrease uu____9952 =
                           match uu____9952 with
                           | (t1,uu____9962) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____9972;
                                       FStar_Syntax_Syntax.vars = uu____9973;_},uu____9974::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10005 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____9916 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10119  ->
                                      match uu____10119 with
                                      | (t1,uu____10129) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10138,(arg,uu____10140)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10169 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10183 -> false in
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
                                           | uu____10331 -> pat in
                                         let uu____10332 =
                                           let uu____10343 =
                                             let uu____10354 =
                                               let uu____10363 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10363, aq) in
                                             [uu____10354] in
                                           ens :: uu____10343 in
                                         req :: uu____10332
                                     | uu____10404 -> rest2
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
        | uu____10426 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___345_10443 = t in
        {
          FStar_Syntax_Syntax.n = (uu___345_10443.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___345_10443.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___346_10477 = b in
             {
               FStar_Parser_AST.b = (uu___346_10477.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___346_10477.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___346_10477.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10536 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10536)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10549 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10549 with
             | (env1,a1) ->
                 let a2 =
                   let uu___347_10559 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___347_10559.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___347_10559.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10581 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10595 =
                     let uu____10598 =
                       let uu____10599 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10599] in
                     no_annot_abs uu____10598 body2 in
                   FStar_All.pipe_left setpos uu____10595 in
                 let uu____10604 =
                   let uu____10605 =
                     let uu____10620 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10621 =
                       let uu____10624 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10624] in
                     (uu____10620, uu____10621) in
                   FStar_Syntax_Syntax.Tm_app uu____10605 in
                 FStar_All.pipe_left mk1 uu____10604)
        | uu____10629 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____10701 = q (rest, pats, body) in
              let uu____10708 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____10701 uu____10708
                FStar_Parser_AST.Formula in
            let uu____10709 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____10709 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____10718 -> failwith "impossible" in
      let uu____10721 =
        let uu____10722 = unparen f in uu____10722.FStar_Parser_AST.tm in
      match uu____10721 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____10729,uu____10730) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____10741,uu____10742) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10773 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____10773
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____10809 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____10809
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____10852 -> desugar_term env f
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
      let uu____10857 =
        FStar_List.fold_left
          (fun uu____10893  ->
             fun b  ->
               match uu____10893 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___348_10945 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___348_10945.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___348_10945.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___348_10945.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____10962 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____10962 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___349_10982 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___349_10982.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___349_10982.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____10999 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____10857 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____11086 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11086)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11091 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11091)
      | FStar_Parser_AST.TVariable x ->
          let uu____11095 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11095)
      | FStar_Parser_AST.NoName t ->
          let uu____11103 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11103)
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
               (fun uu___312_11136  ->
                  match uu___312_11136 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11137 -> false)) in
        let quals2 q =
          let uu____11148 =
            (let uu____11151 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11151) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11148
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11164 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11164;
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
            let uu____11195 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11225  ->
                        match uu____11225 with
                        | (x,uu____11233) ->
                            let uu____11234 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11234 with
                             | (field_name,uu____11242) ->
                                 let only_decl =
                                   ((let uu____11246 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11246)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11248 =
                                        let uu____11249 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11249.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11248) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11263 =
                                       FStar_List.filter
                                         (fun uu___313_11267  ->
                                            match uu___313_11267 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11268 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11263
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___314_11281  ->
                                             match uu___314_11281 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11282 -> false)) in
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
                                      let uu____11290 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11290
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11295 =
                                        let uu____11300 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11300 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11295;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11302 =
                                        let uu____11303 =
                                          let uu____11310 =
                                            let uu____11313 =
                                              let uu____11314 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11314
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11313] in
                                          ((false, [lb]), uu____11310) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11303 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11302;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11195 FStar_List.flatten
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
            (lid,uu____11358,t,uu____11360,n1,uu____11362) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11367 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11367 with
             | (formals,uu____11383) ->
                 (match formals with
                  | [] -> []
                  | uu____11406 ->
                      let filter_records uu___315_11418 =
                        match uu___315_11418 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11421,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11433 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11435 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11435 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11445 = FStar_Util.first_N n1 formals in
                      (match uu____11445 with
                       | (uu____11468,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11494 -> []
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
                    let uu____11544 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11544
                    then
                      let uu____11547 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11547
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11550 =
                      let uu____11555 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11555 in
                    let uu____11556 =
                      let uu____11559 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11559 in
                    let uu____11562 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11550;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11556;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11562
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
          let tycon_id uu___316_11607 =
            match uu___316_11607 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11609,uu____11610) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11620,uu____11621,uu____11622) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11632,uu____11633,uu____11634) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____11664,uu____11665,uu____11666) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____11708) ->
                let uu____11709 =
                  let uu____11710 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11710 in
                FStar_Parser_AST.mk_term uu____11709 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____11712 =
                  let uu____11713 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____11713 in
                FStar_Parser_AST.mk_term uu____11712 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____11715) ->
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
              | uu____11738 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____11744 =
                     let uu____11745 =
                       let uu____11752 = binder_to_term b in
                       (out, uu____11752, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____11745 in
                   FStar_Parser_AST.mk_term uu____11744
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___317_11762 =
            match uu___317_11762 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____11817  ->
                       match uu____11817 with
                       | (x,t,uu____11828) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____11834 =
                    let uu____11835 =
                      let uu____11836 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____11836 in
                    FStar_Parser_AST.mk_term uu____11835
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____11834 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____11840 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____11867  ->
                          match uu____11867 with
                          | (x,uu____11877,uu____11878) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____11840)
            | uu____11931 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___318_11962 =
            match uu___318_11962 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____11986 = typars_of_binders _env binders in
                (match uu____11986 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12032 =
                         let uu____12033 =
                           let uu____12034 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12034 in
                         FStar_Parser_AST.mk_term uu____12033
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12032 binders in
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
            | uu____12047 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12091 =
              FStar_List.fold_left
                (fun uu____12131  ->
                   fun uu____12132  ->
                     match (uu____12131, uu____12132) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12223 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12223 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12091 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12336 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12336
                | uu____12337 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12345 = desugar_abstract_tc quals env [] tc in
              (match uu____12345 with
               | (uu____12358,uu____12359,se,uu____12361) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12364,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12381 =
                                 let uu____12382 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____12382 in
                               if uu____12381
                               then
                                 let uu____12383 =
                                   let uu____12384 =
                                     FStar_Syntax_Print.lid_to_string l in
                                   FStar_Util.format1
                                     "Adding an implicit 'assume new' qualifier on %s"
                                     uu____12384 in
                                 FStar_Errors.warn
                                   se.FStar_Syntax_Syntax.sigrng uu____12383
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12391 ->
                               let uu____12392 =
                                 let uu____12395 =
                                   let uu____12396 =
                                     let uu____12409 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12409) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12396 in
                                 FStar_Syntax_Syntax.mk uu____12395 in
                               uu____12392 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___350_12413 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___350_12413.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___350_12413.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___350_12413.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12416 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12419 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12419
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12434 = typars_of_binders env binders in
              (match uu____12434 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12470 =
                           FStar_Util.for_some
                             (fun uu___319_12472  ->
                                match uu___319_12472 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12473 -> false) quals in
                         if uu____12470
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12480 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___320_12484  ->
                               match uu___320_12484 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12485 -> false)) in
                     if uu____12480
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12494 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12494
                     then
                       let uu____12497 =
                         let uu____12504 =
                           let uu____12505 = unparen t in
                           uu____12505.FStar_Parser_AST.tm in
                         match uu____12504 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12526 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12556)::args_rev ->
                                   let uu____12568 =
                                     let uu____12569 = unparen last_arg in
                                     uu____12569.FStar_Parser_AST.tm in
                                   (match uu____12568 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12597 -> ([], args))
                               | uu____12606 -> ([], args) in
                             (match uu____12526 with
                              | (cattributes,args1) ->
                                  let uu____12645 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12645))
                         | uu____12656 -> (t, []) in
                       match uu____12497 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___321_12678  ->
                                     match uu___321_12678 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____12679 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____12690)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____12714 = tycon_record_as_variant trec in
              (match uu____12714 with
               | (t,fs) ->
                   let uu____12731 =
                     let uu____12734 =
                       let uu____12735 =
                         let uu____12744 =
                           let uu____12747 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____12747 in
                         (uu____12744, fs) in
                       FStar_Syntax_Syntax.RecordType uu____12735 in
                     uu____12734 :: quals in
                   desugar_tycon env d uu____12731 [t])
          | uu____12752::uu____12753 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____12914 = et in
                match uu____12914 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13139 ->
                         let trec = tc in
                         let uu____13163 = tycon_record_as_variant trec in
                         (match uu____13163 with
                          | (t,fs) ->
                              let uu____13222 =
                                let uu____13225 =
                                  let uu____13226 =
                                    let uu____13235 =
                                      let uu____13238 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13238 in
                                    (uu____13235, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13226 in
                                uu____13225 :: quals1 in
                              collect_tcs uu____13222 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13325 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13325 with
                          | (env2,uu____13385,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13534 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13534 with
                          | (env2,uu____13594,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____13719 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____13766 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____13766 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___323_14277  ->
                             match uu___323_14277 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14344,uu____14345);
                                    FStar_Syntax_Syntax.sigrng = uu____14346;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14347;
                                    FStar_Syntax_Syntax.sigmeta = uu____14348;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14349;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14410 =
                                     typars_of_binders env1 binders in
                                   match uu____14410 with
                                   | (env2,tpars1) ->
                                       let uu____14441 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14441 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14474 =
                                   let uu____14495 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14495) in
                                 [uu____14474]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14563);
                                    FStar_Syntax_Syntax.sigrng = uu____14564;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14566;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14567;_},constrs,tconstr,quals1)
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
                                 let uu____14663 = push_tparams env1 tpars in
                                 (match uu____14663 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____14740  ->
                                             match uu____14740 with
                                             | (x,uu____14754) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____14762 =
                                        let uu____14791 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____14905  ->
                                                  match uu____14905 with
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
                                                        let uu____14961 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____14961 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___322_14972
                                                                 ->
                                                                match uu___322_14972
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____14984
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____14992 =
                                                        let uu____15013 =
                                                          let uu____15014 =
                                                            let uu____15015 =
                                                              let uu____15030
                                                                =
                                                                let uu____15033
                                                                  =
                                                                  let uu____15036
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15036 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15033 in
                                                              (name, univs1,
                                                                uu____15030,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15015 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15014;
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
                                                          uu____15013) in
                                                      (name, uu____14992))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____14791 in
                                      (match uu____14762 with
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
                             | uu____15275 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15407  ->
                             match uu____15407 with
                             | (name_doc,uu____15435,uu____15436) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15516  ->
                             match uu____15516 with
                             | (uu____15537,uu____15538,se) -> se)) in
                   let uu____15568 =
                     let uu____15575 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15575 rng in
                   (match uu____15568 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____15641  ->
                                  match uu____15641 with
                                  | (uu____15664,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____15715,tps,k,uu____15718,constrs)
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
                                  | uu____15737 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____15754  ->
                                 match uu____15754 with
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
      let uu____15789 =
        FStar_List.fold_left
          (fun uu____15812  ->
             fun b  ->
               match uu____15812 with
               | (env1,binders1) ->
                   let uu____15832 = desugar_binder env1 b in
                   (match uu____15832 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15849 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____15849 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____15866 ->
                        FStar_Exn.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____15789 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let push_reflect_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_ToSyntax_Env.env
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____15911 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___324_15916  ->
                    match uu___324_15916 with
                    | FStar_Syntax_Syntax.Reflectable uu____15917 -> true
                    | uu____15918 -> false)) in
          if uu____15911
          then
            let monad_env =
              FStar_ToSyntax_Env.enter_monad_scope env
                effect_name.FStar_Ident.ident in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
                (FStar_ToSyntax_Env.qualify monad_env) in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name] in
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
              } in
            FStar_ToSyntax_Env.push_sigelt env refl_decl
          else env
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
                let uu____16017 = desugar_binders monad_env eff_binders in
                match uu____16017 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16038 =
                        let uu____16039 =
                          let uu____16046 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16046 in
                        FStar_List.length uu____16039 in
                      uu____16038 = (Prims.parse_int "1") in
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
                          (uu____16088,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16090,uu____16091,uu____16092),uu____16093)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16126 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16127 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16139 = name_of_eff_decl decl in
                           FStar_List.mem uu____16139 mandatory_members)
                        eff_decls in
                    (match uu____16127 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16156 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16185  ->
                                   fun decl  ->
                                     match uu____16185 with
                                     | (env2,out) ->
                                         let uu____16205 =
                                           desugar_decl env2 decl in
                                         (match uu____16205 with
                                          | (env3,ses) ->
                                              let uu____16218 =
                                                let uu____16221 =
                                                  FStar_List.hd ses in
                                                uu____16221 :: out in
                                              (env3, uu____16218)))
                                (env1, [])) in
                         (match uu____16156 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16289,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16292,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16293,
                                                                (def,uu____16295)::
                                                                (cps_type,uu____16297)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16298;
                                                             FStar_Parser_AST.level
                                                               = uu____16299;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16351 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16351 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16371 =
                                                   let uu____16372 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16373 =
                                                     let uu____16374 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16374 in
                                                   let uu____16379 =
                                                     let uu____16380 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16380 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16372;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16373;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16379
                                                   } in
                                                 (uu____16371, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16387,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16390,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16425 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16425 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16445 =
                                                   let uu____16446 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16447 =
                                                     let uu____16448 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16448 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16446;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16447;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16445, doc1))
                                        | uu____16455 ->
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
                                let uu____16485 =
                                  let uu____16486 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16486 in
                                ([], uu____16485) in
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
                                    let uu____16503 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16503) in
                                  let uu____16510 =
                                    let uu____16511 =
                                      let uu____16512 =
                                        let uu____16513 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16513 in
                                      let uu____16522 = lookup "return" in
                                      let uu____16523 = lookup "bind" in
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
                                          uu____16512;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16522;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16523;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16511 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16510;
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
                                       (fun uu___325_16527  ->
                                          match uu___325_16527 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16528 -> true
                                          | uu____16529 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16539 =
                                     let uu____16540 =
                                       let uu____16541 = lookup "return_wp" in
                                       let uu____16542 = lookup "bind_wp" in
                                       let uu____16543 =
                                         lookup "if_then_else" in
                                       let uu____16544 = lookup "ite_wp" in
                                       let uu____16545 = lookup "stronger" in
                                       let uu____16546 = lookup "close_wp" in
                                       let uu____16547 = lookup "assert_p" in
                                       let uu____16548 = lookup "assume_p" in
                                       let uu____16549 = lookup "null_wp" in
                                       let uu____16550 = lookup "trivial" in
                                       let uu____16551 =
                                         if rr
                                         then
                                           let uu____16552 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16552
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16568 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16570 =
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
                                           uu____16541;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16542;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16543;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16544;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16545;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16546;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16547;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16548;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16549;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16550;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16551;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16568;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16570;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16540 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16539;
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
                                        fun uu____16595  ->
                                          match uu____16595 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16609 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16609 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                push_reflect_effect env5 qualifiers mname
                                  d.FStar_Parser_AST.drange in
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
                let uu____16633 = desugar_binders env1 eff_binders in
                match uu____16633 with
                | (env2,binders) ->
                    let uu____16652 =
                      let uu____16671 = head_and_args defn in
                      match uu____16671 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____16716 ->
                                let uu____16717 =
                                  let uu____16718 =
                                    let uu____16723 =
                                      let uu____16724 =
                                        let uu____16725 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____16725 " not found" in
                                      Prims.strcat "Effect " uu____16724 in
                                    (uu____16723,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____16718 in
                                FStar_Exn.raise uu____16717 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____16727 =
                            match FStar_List.rev args with
                            | (last_arg,uu____16757)::args_rev ->
                                let uu____16769 =
                                  let uu____16770 = unparen last_arg in
                                  uu____16770.FStar_Parser_AST.tm in
                                (match uu____16769 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____16798 -> ([], args))
                            | uu____16807 -> ([], args) in
                          (match uu____16727 with
                           | (cattributes,args1) ->
                               let uu____16858 = desugar_args env2 args1 in
                               let uu____16867 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____16858, uu____16867)) in
                    (match uu____16652 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Exn.raise
                              (FStar_Errors.Error
                                 ("Unexpected number of arguments to effect constructor",
                                   (defn.FStar_Parser_AST.range)))
                          else ();
                          (let uu____16923 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____16923 with
                           | (ed_binders,uu____16937,ed_binders_opening) ->
                               let sub1 uu____16948 =
                                 match uu____16948 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____16962 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____16962 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____16966 =
                                       let uu____16967 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____16967) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____16966 in
                               let mname =
                                 FStar_ToSyntax_Env.qualify env0 eff_name in
                               let ed1 =
                                 let uu____16972 =
                                   let uu____16973 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature)) in
                                   FStar_Pervasives_Native.snd uu____16973 in
                                 let uu____16984 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp in
                                 let uu____16985 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp in
                                 let uu____16986 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else in
                                 let uu____16987 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp in
                                 let uu____16988 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger in
                                 let uu____16989 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp in
                                 let uu____16990 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p in
                                 let uu____16991 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p in
                                 let uu____16992 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp in
                                 let uu____16993 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial in
                                 let uu____16994 =
                                   let uu____16995 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                                   FStar_Pervasives_Native.snd uu____16995 in
                                 let uu____17006 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr in
                                 let uu____17007 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr in
                                 let uu____17008 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17016 =
                                          FStar_ToSyntax_Env.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____17017 =
                                          let uu____17018 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____17018 in
                                        let uu____17029 =
                                          let uu____17030 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____17030 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17016;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17017;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17029
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____16972;
                                   FStar_Syntax_Syntax.ret_wp = uu____16984;
                                   FStar_Syntax_Syntax.bind_wp = uu____16985;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____16986;
                                   FStar_Syntax_Syntax.ite_wp = uu____16987;
                                   FStar_Syntax_Syntax.stronger = uu____16988;
                                   FStar_Syntax_Syntax.close_wp = uu____16989;
                                   FStar_Syntax_Syntax.assert_p = uu____16990;
                                   FStar_Syntax_Syntax.assume_p = uu____16991;
                                   FStar_Syntax_Syntax.null_wp = uu____16992;
                                   FStar_Syntax_Syntax.trivial = uu____16993;
                                   FStar_Syntax_Syntax.repr = uu____16994;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17006;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17007;
                                   FStar_Syntax_Syntax.actions = uu____17008
                                 } in
                               let se =
                                 let for_free =
                                   let uu____17043 =
                                     let uu____17044 =
                                       let uu____17051 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature in
                                       FStar_Pervasives_Native.fst
                                         uu____17051 in
                                     FStar_List.length uu____17044 in
                                   uu____17043 = (Prims.parse_int "1") in
                                 let uu____17080 =
                                   let uu____17083 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.map uu____17083 quals in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17080;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 } in
                               let monad_env = env2 in
                               let env3 =
                                 FStar_ToSyntax_Env.push_sigelt env0 se in
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
                                             FStar_ToSyntax_Env.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name in
                                           let env6 =
                                             let uu____17103 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a in
                                             FStar_ToSyntax_Env.push_sigelt
                                               env5 uu____17103 in
                                           FStar_ToSyntax_Env.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4) in
                               let env6 =
                                 let uu____17105 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____17105
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
                               (env7, [se]))))
and mk_comment_attr:
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun d  ->
    let uu____17120 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____17120 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17171 ->
              let uu____17172 =
                let uu____17173 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17173 in
              Prims.strcat "\n  " uu____17172
          | uu____17174 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____17187  ->
               match uu____17187 with
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
          let uu____17205 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____17205
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____17207 =
          let uu____17216 = FStar_Syntax_Syntax.as_arg arg in [uu____17216] in
        FStar_Syntax_Util.mk_app fv uu____17207
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17223 = desugar_decl_noattrs env d in
      match uu____17223 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____17243 = mk_comment_attr d in uu____17243 :: attrs1 in
          let uu____17248 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___351_17254 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___351_17254.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___351_17254.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___351_17254.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___351_17254.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____17248)
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
      | FStar_Parser_AST.Fsdoc uu____17280 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17296 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17296, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17335  ->
                 match uu____17335 with | (x,uu____17343) -> x) tcs in
          let uu____17348 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17348 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17370;
                    FStar_Parser_AST.prange = uu____17371;_},uu____17372)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17381;
                    FStar_Parser_AST.prange = uu____17382;_},uu____17383)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17398;
                         FStar_Parser_AST.prange = uu____17399;_},uu____17400);
                    FStar_Parser_AST.prange = uu____17401;_},uu____17402)::[]
                   -> false
               | (p,uu____17418)::[] ->
                   let uu____17427 = is_app_pattern p in
                   Prims.op_Negation uu____17427
               | uu____17428 -> false) in
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
            let uu____17447 =
              let uu____17448 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17448.FStar_Syntax_Syntax.n in
            (match uu____17447 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17456) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17489::uu____17490 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17493 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___326_17506  ->
                               match uu___326_17506 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17509;
                                   FStar_Syntax_Syntax.lbunivs = uu____17510;
                                   FStar_Syntax_Syntax.lbtyp = uu____17511;
                                   FStar_Syntax_Syntax.lbeff = uu____17512;
                                   FStar_Syntax_Syntax.lbdef = uu____17513;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17521;
                                   FStar_Syntax_Syntax.lbtyp = uu____17522;
                                   FStar_Syntax_Syntax.lbeff = uu____17523;
                                   FStar_Syntax_Syntax.lbdef = uu____17524;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17534 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17548  ->
                             match uu____17548 with
                             | (uu____17553,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17534
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17565 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17565
                   then
                     let uu____17574 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___352_17588 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___353_17590 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___353_17590.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___353_17590.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___352_17588.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___352_17588.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___352_17588.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___352_17588.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17574)
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
             | uu____17622 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17628 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17647 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17628 with
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
                       let uu___354_17671 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___354_17671.FStar_Parser_AST.prange)
                       }
                   | uu____17672 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___355_17679 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___355_17679.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___355_17679.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___355_17679.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17711 id =
                   match uu____17711 with
                   | (env1,ses) ->
                       let main =
                         let uu____17732 =
                           let uu____17733 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17733 in
                         FStar_Parser_AST.mk_term uu____17732
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
                       let uu____17783 = desugar_decl env1 id_decl in
                       (match uu____17783 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17801 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17801 FStar_Util.set_elements in
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
            let uu____17832 = close_fun env t in desugar_term env uu____17832 in
          let quals1 =
            let uu____17836 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____17836
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____17842 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____17842;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____17854 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____17854 with
           | (t,uu____17868) ->
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
            let uu____17902 =
              let uu____17909 = FStar_Syntax_Syntax.null_binder t in
              [uu____17909] in
            let uu____17910 =
              let uu____17913 =
                let uu____17914 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____17914 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17913 in
            FStar_Syntax_Util.arrow uu____17902 uu____17910 in
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
            let uu____17976 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____17976 with
            | FStar_Pervasives_Native.None  ->
                let uu____17979 =
                  let uu____17980 =
                    let uu____17985 =
                      let uu____17986 =
                        let uu____17987 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____17987 " not found" in
                      Prims.strcat "Effect name " uu____17986 in
                    (uu____17985, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____17980 in
                FStar_Exn.raise uu____17979
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____17991 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18033 =
                  let uu____18042 =
                    let uu____18049 = desugar_term env t in ([], uu____18049) in
                  FStar_Pervasives_Native.Some uu____18042 in
                (uu____18033, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18082 =
                  let uu____18091 =
                    let uu____18098 = desugar_term env wp in
                    ([], uu____18098) in
                  FStar_Pervasives_Native.Some uu____18091 in
                let uu____18107 =
                  let uu____18116 =
                    let uu____18123 = desugar_term env t in ([], uu____18123) in
                  FStar_Pervasives_Native.Some uu____18116 in
                (uu____18082, uu____18107)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18149 =
                  let uu____18158 =
                    let uu____18165 = desugar_term env t in ([], uu____18165) in
                  FStar_Pervasives_Native.Some uu____18158 in
                (FStar_Pervasives_Native.None, uu____18149) in
          (match uu____17991 with
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
      let uu____18253 =
        FStar_List.fold_left
          (fun uu____18273  ->
             fun d  ->
               match uu____18273 with
               | (env1,sigelts) ->
                   let uu____18293 = desugar_decl env1 d in
                   (match uu____18293 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____18253 with
      | (env1,sigelts) ->
          let rec forward acc uu___328_18334 =
            match uu___328_18334 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18348,FStar_Syntax_Syntax.Sig_let uu____18349) ->
                     let uu____18362 =
                       let uu____18365 =
                         let uu___356_18366 = se2 in
                         let uu____18367 =
                           let uu____18370 =
                             FStar_List.filter
                               (fun uu___327_18384  ->
                                  match uu___327_18384 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18388;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18389;_},uu____18390);
                                      FStar_Syntax_Syntax.pos = uu____18391;
                                      FStar_Syntax_Syntax.vars = uu____18392;_}
                                      when
                                      let uu____18415 =
                                        let uu____18416 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____18416 in
                                      uu____18415 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18417 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____18370
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___356_18366.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___356_18366.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___356_18366.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___356_18366.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18367
                         } in
                       uu____18365 :: se1 :: acc in
                     forward uu____18362 sigelts1
                 | uu____18422 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____18430 = forward [] sigelts in (env1, uu____18430)
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
          | (FStar_Pervasives_Native.None ,uu____18481) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18485;
               FStar_Syntax_Syntax.exports = uu____18486;
               FStar_Syntax_Syntax.is_interface = uu____18487;_},FStar_Parser_AST.Module
             (current_lid,uu____18489)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18497) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18500 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18536 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18536, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18553 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname FStar_ToSyntax_Env.default_mii in
              (uu____18553, mname, decls, false) in
        match uu____18500 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18583 = desugar_decls env2 decls in
            (match uu____18583 with
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
          let uu____18637 =
            (FStar_Options.interactive ()) &&
              (let uu____18639 =
                 let uu____18640 =
                   let uu____18641 = FStar_Options.file_list () in
                   FStar_List.hd uu____18641 in
                 FStar_Util.get_file_extension uu____18640 in
               FStar_List.mem uu____18639 ["fsti"; "fsi"]) in
          if uu____18637 then as_interface m else m in
        let uu____18645 = desugar_modul_common curmod env m1 in
        match uu____18645 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18660 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18676 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18676 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18692 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18692
            then
              let uu____18693 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18693
            else ());
           (let uu____18695 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18695, modul)))
let ast_modul_to_modul:
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun env  ->
      let uu____18709 = desugar_modul env modul in
      match uu____18709 with | (env1,modul1) -> (modul1, env1)
let decls_to_sigelts:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv
  =
  fun decls  ->
    fun env  ->
      let uu____18736 = desugar_decls env decls in
      match uu____18736 with | (env1,sigelts) -> (sigelts, env1)
let partial_ast_modul_to_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____18774 = desugar_partial_modul modul env a_modul in
        match uu____18774 with | (env1,modul1) -> (modul1, env1)
let add_modul_to_env:
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
              | uu____18848 ->
                  let t =
                    let uu____18856 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange in
                    erase_univs uu____18856 in
                  let uu____18865 =
                    let uu____18866 = FStar_Syntax_Subst.compress t in
                    uu____18866.FStar_Syntax_Syntax.n in
                  (match uu____18865 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____18876,uu____18877)
                       -> bs1
                   | uu____18898 -> failwith "Impossible") in
            let uu____18905 =
              let uu____18912 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____18912
                FStar_Syntax_Syntax.t_unit in
            match uu____18905 with
            | (binders,uu____18914,binders_opening) ->
                let erase_term t =
                  let uu____18920 =
                    let uu____18921 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____18921 in
                  FStar_Syntax_Subst.close binders uu____18920 in
                let erase_tscheme uu____18937 =
                  match uu____18937 with
                  | (us,t) ->
                      let t1 =
                        let uu____18957 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____18957 t in
                      let uu____18960 =
                        let uu____18961 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____18961 in
                      ([], uu____18960) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____18990 ->
                        let bs =
                          let uu____18998 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____18998 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange in
                        let uu____19028 =
                          let uu____19029 =
                            let uu____19032 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____19032 in
                          uu____19029.FStar_Syntax_Syntax.n in
                        (match uu____19028 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19040,uu____19041) -> bs1
                         | uu____19062 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____19073 =
                      let uu____19074 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____19074 in
                    FStar_Syntax_Subst.close binders uu____19073 in
                  let uu___357_19075 = action in
                  let uu____19076 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____19077 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___357_19075.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___357_19075.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19076;
                    FStar_Syntax_Syntax.action_typ = uu____19077
                  } in
                let uu___358_19078 = ed in
                let uu____19079 = FStar_Syntax_Subst.close_binders binders in
                let uu____19080 = erase_term ed.FStar_Syntax_Syntax.signature in
                let uu____19081 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                let uu____19082 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                let uu____19083 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                let uu____19084 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                let uu____19085 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger in
                let uu____19086 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp in
                let uu____19087 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p in
                let uu____19088 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p in
                let uu____19089 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp in
                let uu____19090 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial in
                let uu____19091 = erase_term ed.FStar_Syntax_Syntax.repr in
                let uu____19092 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr in
                let uu____19093 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                let uu____19094 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___358_19078.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___358_19078.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19079;
                  FStar_Syntax_Syntax.signature = uu____19080;
                  FStar_Syntax_Syntax.ret_wp = uu____19081;
                  FStar_Syntax_Syntax.bind_wp = uu____19082;
                  FStar_Syntax_Syntax.if_then_else = uu____19083;
                  FStar_Syntax_Syntax.ite_wp = uu____19084;
                  FStar_Syntax_Syntax.stronger = uu____19085;
                  FStar_Syntax_Syntax.close_wp = uu____19086;
                  FStar_Syntax_Syntax.assert_p = uu____19087;
                  FStar_Syntax_Syntax.assume_p = uu____19088;
                  FStar_Syntax_Syntax.null_wp = uu____19089;
                  FStar_Syntax_Syntax.trivial = uu____19090;
                  FStar_Syntax_Syntax.repr = uu____19091;
                  FStar_Syntax_Syntax.return_repr = uu____19092;
                  FStar_Syntax_Syntax.bind_repr = uu____19093;
                  FStar_Syntax_Syntax.actions = uu____19094
                } in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___359_19106 = se in
                  let uu____19107 =
                    let uu____19108 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19108 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19107;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___359_19106.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___359_19106.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___359_19106.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___359_19106.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___360_19112 = se in
                  let uu____19113 =
                    let uu____19114 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19114 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19113;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___360_19112.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___360_19112.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___360_19112.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___360_19112.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19116 -> FStar_ToSyntax_Env.push_sigelt env se in
          let uu____19117 =
            FStar_ToSyntax_Env.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____19117 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19129 =
                  FStar_ToSyntax_Env.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt1 uu____19129
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_ToSyntax_Env.finish en2 m in
              let uu____19131 =
                if pop_when_done
                then
                  FStar_ToSyntax_Env.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____19131)