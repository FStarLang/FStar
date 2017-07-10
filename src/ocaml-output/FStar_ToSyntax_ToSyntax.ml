open Prims
let desugar_disjunctive_pattern:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.branch Prims.list
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
  fun uu___200_46  ->
    match uu___200_46 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____49 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___201_63  ->
        match uu___201_63 with
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
                 raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline  ->
            raise (FStar_Errors.Error ("Unsupported qualifier", r))
        | FStar_Parser_AST.Visible  ->
            raise (FStar_Errors.Error ("Unsupported qualifier", r))
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___202_70  ->
    match uu___202_70 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___203_78  ->
    match uu___203_78 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____80 -> FStar_Pervasives_Native.None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  ->
      (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
  | uu____119 -> (t, FStar_Pervasives_Native.None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____131 -> true
            | uu____134 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____140 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____145 =
      let uu____146 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____146 in
    FStar_Parser_AST.mk_term uu____145 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____151 =
      let uu____152 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____152 in
    FStar_Parser_AST.mk_term uu____151 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____162 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____162 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____166) ->
          let uu____173 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____173 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____177,uu____178) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____181,uu____182) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____185,t1) -> is_comp_type env t1
      | uu____187 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____200 =
          let uu____202 =
            let uu____203 =
              let uu____206 = FStar_Parser_AST.compile_op n1 s in
              (uu____206, r) in
            FStar_Ident.mk_ident uu____203 in
          [uu____202] in
        FStar_All.pipe_right uu____200 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____244 =
      let uu____245 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
          FStar_Pervasives_Native.None in
      FStar_All.pipe_right uu____245 FStar_Syntax_Syntax.fv_to_tm in
    FStar_Pervasives_Native.Some uu____244 in
  let fallback uu____250 =
    match FStar_Ident.text_of_id op with
    | "=" -> r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.Delta_equational
    | ":=" ->
        r FStar_Parser_Const.write_lid FStar_Syntax_Syntax.Delta_equational
    | "<" -> r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.Delta_equational
    | "<=" ->
        r FStar_Parser_Const.op_LTE FStar_Syntax_Syntax.Delta_equational
    | ">" -> r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.Delta_equational
    | ">=" ->
        r FStar_Parser_Const.op_GTE FStar_Syntax_Syntax.Delta_equational
    | "&&" ->
        r FStar_Parser_Const.op_And FStar_Syntax_Syntax.Delta_equational
    | "||" -> r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.Delta_equational
    | "+" ->
        r FStar_Parser_Const.op_Addition FStar_Syntax_Syntax.Delta_equational
    | "-" when arity = (Prims.parse_int "1") ->
        r FStar_Parser_Const.op_Minus FStar_Syntax_Syntax.Delta_equational
    | "-" ->
        r FStar_Parser_Const.op_Subtraction
          FStar_Syntax_Syntax.Delta_equational
    | "/" ->
        r FStar_Parser_Const.op_Division FStar_Syntax_Syntax.Delta_equational
    | "%" ->
        r FStar_Parser_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational
    | "!" ->
        r FStar_Parser_Const.read_lid FStar_Syntax_Syntax.Delta_equational
    | "@" ->
        let uu____252 = FStar_Options.ml_ish () in
        if uu____252
        then
          r FStar_Parser_Const.list_append_lid
            FStar_Syntax_Syntax.Delta_equational
        else
          r FStar_Parser_Const.list_tot_append_lid
            FStar_Syntax_Syntax.Delta_equational
    | "^" ->
        r FStar_Parser_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational
    | "|>" ->
        r FStar_Parser_Const.pipe_right_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<|" ->
        r FStar_Parser_Const.pipe_left_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<>" ->
        r FStar_Parser_Const.op_notEq FStar_Syntax_Syntax.Delta_equational
    | "~" ->
        r FStar_Parser_Const.not_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "==" ->
        r FStar_Parser_Const.eq2_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "<<" ->
        r FStar_Parser_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant
    | "/\\" ->
        r FStar_Parser_Const.and_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "\\/" ->
        r FStar_Parser_Const.or_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "==>" ->
        r FStar_Parser_Const.imp_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "<==>" ->
        r FStar_Parser_Const.iff_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | uu____255 -> FStar_Pervasives_Native.None in
  let uu____256 =
    let uu____260 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____260 in
  match uu____256 with
  | FStar_Pervasives_Native.Some t ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
  | uu____267 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____278 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____278
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____307 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____310 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____310 with | (env1,uu____317) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____319,term) ->
          let uu____321 = free_type_vars env term in (env, uu____321)
      | FStar_Parser_AST.TAnnotated (id,uu____325) ->
          let uu____326 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____326 with | (env1,uu____333) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____336 = free_type_vars env t in (env, uu____336)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____341 =
        let uu____342 = unparen t in uu____342.FStar_Parser_AST.tm in
      match uu____341 with
      | FStar_Parser_AST.Labeled uu____344 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____350 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____350 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____357 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____361 -> []
      | FStar_Parser_AST.Uvar uu____362 -> []
      | FStar_Parser_AST.Var uu____363 -> []
      | FStar_Parser_AST.Projector uu____364 -> []
      | FStar_Parser_AST.Discrim uu____367 -> []
      | FStar_Parser_AST.Name uu____368 -> []
      | FStar_Parser_AST.Assign (uu____369,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____372) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____376) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____379,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____391,ts) ->
          FStar_List.collect
            (fun uu____404  ->
               match uu____404 with | (t1,uu____409) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____410,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____416) ->
          let uu____417 = free_type_vars env t1 in
          let uu____419 = free_type_vars env t2 in
          FStar_List.append uu____417 uu____419
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____423 = free_type_vars_b env b in
          (match uu____423 with
           | (env1,f) ->
               let uu____432 = free_type_vars env1 t1 in
               FStar_List.append f uu____432)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____438 =
            FStar_List.fold_left
              (fun uu____452  ->
                 fun binder  ->
                   match uu____452 with
                   | (env1,free) ->
                       let uu____464 = free_type_vars_b env1 binder in
                       (match uu____464 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____438 with
           | (env1,free) ->
               let uu____482 = free_type_vars env1 body in
               FStar_List.append free uu____482)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____488 =
            FStar_List.fold_left
              (fun uu____502  ->
                 fun binder  ->
                   match uu____502 with
                   | (env1,free) ->
                       let uu____514 = free_type_vars_b env1 binder in
                       (match uu____514 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____488 with
           | (env1,free) ->
               let uu____532 = free_type_vars env1 body in
               FStar_List.append free uu____532)
      | FStar_Parser_AST.Project (t1,uu____535) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____538 -> []
      | FStar_Parser_AST.Let uu____542 -> []
      | FStar_Parser_AST.LetOpen uu____549 -> []
      | FStar_Parser_AST.If uu____552 -> []
      | FStar_Parser_AST.QForall uu____556 -> []
      | FStar_Parser_AST.QExists uu____563 -> []
      | FStar_Parser_AST.Record uu____570 -> []
      | FStar_Parser_AST.Match uu____577 -> []
      | FStar_Parser_AST.TryWith uu____585 -> []
      | FStar_Parser_AST.Bind uu____593 -> []
      | FStar_Parser_AST.Seq uu____597 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____627 =
        let uu____628 = unparen t1 in uu____628.FStar_Parser_AST.tm in
      match uu____627 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____652 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____668 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____668 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____684 =
                     let uu____685 =
                       let uu____688 = tm_type x.FStar_Ident.idRange in
                       (x, uu____688) in
                     FStar_Parser_AST.TAnnotated uu____685 in
                   FStar_Parser_AST.mk_binder uu____684 x.FStar_Ident.idRange
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
        let uu____701 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____701 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____717 =
                     let uu____718 =
                       let uu____721 = tm_type x.FStar_Ident.idRange in
                       (x, uu____721) in
                     FStar_Parser_AST.TAnnotated uu____718 in
                   FStar_Parser_AST.mk_binder uu____717 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____723 =
             let uu____724 = unparen t in uu____724.FStar_Parser_AST.tm in
           match uu____723 with
           | FStar_Parser_AST.Product uu____725 -> t
           | uu____729 ->
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
      | uu____752 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____758,uu____759) -> true
    | FStar_Parser_AST.PatVar (uu____762,uu____763) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____767) -> is_var_pattern p1
    | uu____768 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____774) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____775;
           FStar_Parser_AST.prange = uu____776;_},uu____777)
        -> true
    | uu____783 -> false
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
    | uu____788 -> p
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
            let uu____817 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____817 with
             | (name,args,uu____834) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____848);
               FStar_Parser_AST.prange = uu____849;_},args)
            when is_top_level1 ->
            let uu____855 =
              let uu____858 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____858 in
            (uu____855, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____864);
               FStar_Parser_AST.prange = uu____865;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____875 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____901 -> acc
      | FStar_Parser_AST.PatVar
          (uu____902,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____904 -> acc
      | FStar_Parser_AST.PatTvar uu____905 -> acc
      | FStar_Parser_AST.PatOp uu____909 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____915) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____921) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____930 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____930
      | FStar_Parser_AST.PatAscribed (pat,uu____935) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____948  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____969 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____991 -> false
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
  fun uu___204_1011  ->
    match uu___204_1011 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1016 -> failwith "Impossible"
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
      fun uu___205_1036  ->
        match uu___205_1036 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1045 = FStar_Syntax_Syntax.null_binder k in
            (uu____1045, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1049 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1049 with
             | (env1,a1) ->
                 (((let uu___226_1061 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___226_1061.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___226_1061.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1075  ->
    match uu____1075 with
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
let mk_ref_read tm =
  let tm' =
    let uu____1124 =
      let uu____1134 =
        let uu____1135 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1135 in
      let uu____1136 =
        let uu____1142 =
          let uu____1147 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1147) in
        [uu____1142] in
      (uu____1134, uu____1136) in
    FStar_Syntax_Syntax.Tm_app uu____1124 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1183 =
      let uu____1193 =
        let uu____1194 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1194 in
      let uu____1195 =
        let uu____1201 =
          let uu____1206 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1206) in
        [uu____1201] in
      (uu____1193, uu____1195) in
    FStar_Syntax_Syntax.Tm_app uu____1183 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1258 =
      let uu____1268 =
        let uu____1269 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1269 in
      let uu____1270 =
        let uu____1276 =
          let uu____1281 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1281) in
        let uu____1284 =
          let uu____1290 =
            let uu____1295 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1295) in
          [uu____1290] in
        uu____1276 :: uu____1284 in
      (uu____1268, uu____1270) in
    FStar_Syntax_Syntax.Tm_app uu____1258 in
  FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___206_1322  ->
    match uu___206_1322 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1323 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1333 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1333)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1346 =
      let uu____1347 = unparen t in uu____1347.FStar_Parser_AST.tm in
    match uu____1346 with
    | FStar_Parser_AST.Wild  ->
        let uu____1350 =
          let uu____1351 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1351 in
        FStar_Util.Inr uu____1350
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1358)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < (Prims.parse_int "0")
         then
           raise
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
             let uu____1398 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1398
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1405 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1405
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1412 =
               let uu____1413 =
                 let uu____1416 =
                   let uu____1417 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1417 in
                 (uu____1416, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1413 in
             raise uu____1412)
    | FStar_Parser_AST.App uu____1420 ->
        let rec aux t1 univargs =
          let uu____1439 =
            let uu____1440 = unparen t1 in uu____1440.FStar_Parser_AST.tm in
          match uu____1439 with
          | FStar_Parser_AST.App (t2,targ,uu____1445) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___207_1460  ->
                     match uu___207_1460 with
                     | FStar_Util.Inr uu____1463 -> true
                     | uu____1464 -> false) univargs
              then
                let uu____1467 =
                  let uu____1468 =
                    FStar_List.map
                      (fun uu___208_1474  ->
                         match uu___208_1474 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1468 in
                FStar_Util.Inr uu____1467
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___209_1486  ->
                        match uu___209_1486 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1490 -> failwith "impossible")
                     univargs in
                 let uu____1491 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1491)
          | uu____1497 ->
              let uu____1498 =
                let uu____1499 =
                  let uu____1502 =
                    let uu____1503 =
                      let uu____1504 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1504 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1503 in
                  (uu____1502, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1499 in
              raise uu____1498 in
        aux t []
    | uu____1509 ->
        let uu____1510 =
          let uu____1511 =
            let uu____1514 =
              let uu____1515 =
                let uu____1516 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1516 " in universe context" in
              Prims.strcat "Unexpected term " uu____1515 in
            (uu____1514, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1511 in
        raise uu____1510
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1555 = FStar_List.hd fields in
  match uu____1555 with
  | (f,uu____1561) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1569 =
          match uu____1569 with
          | (f',uu____1573) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1575 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1575
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1579 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1579);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1739 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1744 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1745 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1747,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1771  ->
                          match uu____1771 with
                          | (p3,uu____1777) ->
                              let uu____1778 = pat_vars p3 in
                              FStar_Util.set_union out uu____1778)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1781) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1782) -> ()
         | (true ,uu____1786) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1814 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1814 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____1823 ->
               let uu____1825 = push_bv_maybe_mut e x in
               (match uu____1825 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1869 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1878 =
                 let uu____1879 =
                   let uu____1880 =
                     let uu____1884 =
                       let uu____1885 =
                         let uu____1888 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1888, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1885 in
                     (uu____1884, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____1880 in
                 {
                   FStar_Parser_AST.pat = uu____1879;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1878
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1892 = aux loc env1 p2 in
               (match uu____1892 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1913 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1919 = close_fun env1 t in
                            desugar_term env1 uu____1919 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1921 -> true)
                           then
                             (let uu____1922 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1923 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1924 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1922 uu____1923 uu____1924)
                           else ();
                           LocalBinder
                             (((let uu___227_1927 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___227_1927.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___227_1927.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1930 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1930, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1937 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1937, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1950 = resolvex loc env1 x in
               (match uu____1950 with
                | (loc1,env2,xbv) ->
                    let uu____1963 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1963, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1976 = resolvex loc env1 x in
               (match uu____1976 with
                | (loc1,env2,xbv) ->
                    let uu____1989 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1989, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1997 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1997, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2010;_},args)
               ->
               let uu____2014 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2041  ->
                        match uu____2041 with
                        | (loc1,env2,args1) ->
                            let uu____2067 = aux loc1 env2 arg in
                            (match uu____2067 with
                             | (loc2,env3,uu____2083,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2014 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2122 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____2122, false))
           | FStar_Parser_AST.PatApp uu____2131 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2143 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2166  ->
                        match uu____2166 with
                        | (loc1,env2,pats1) ->
                            let uu____2184 = aux loc1 env2 pat in
                            (match uu____2184 with
                             | (loc2,env3,uu____2198,pat1,uu____2200) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2143 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2224 =
                        let uu____2226 =
                          let uu____2230 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2230 in
                        let uu____2231 =
                          let uu____2232 =
                            let uu____2239 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2239, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2232 in
                        FStar_All.pipe_left uu____2226 uu____2231 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2259 =
                               let uu____2260 =
                                 let uu____2267 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2267, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2260 in
                             FStar_All.pipe_left (pos_r r) uu____2259) pats1
                        uu____2224 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2291 =
                 FStar_List.fold_left
                   (fun uu____2317  ->
                      fun p2  ->
                        match uu____2317 with
                        | (loc1,env2,pats) ->
                            let uu____2344 = aux loc1 env2 p2 in
                            (match uu____2344 with
                             | (loc2,env3,uu____2360,pat,uu____2362) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2291 with
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
                    let uu____2425 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2425 with
                     | (constr,uu____2437) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2440 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2442 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____2442, false)))
           | FStar_Parser_AST.PatRecord [] ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2481  ->
                         match uu____2481 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2500  ->
                         match uu____2500 with
                         | (f,uu____2504) ->
                             let uu____2505 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2520  ->
                                       match uu____2520 with
                                       | (g,uu____2524) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2505 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____2527,p2)
                                  -> p2))) in
               let app =
                 let uu____2532 =
                   let uu____2533 =
                     let uu____2537 =
                       let uu____2538 =
                         let uu____2539 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2539 in
                       FStar_Parser_AST.mk_pattern uu____2538
                         p1.FStar_Parser_AST.prange in
                     (uu____2537, args) in
                   FStar_Parser_AST.PatApp uu____2533 in
                 FStar_Parser_AST.mk_pattern uu____2532
                   p1.FStar_Parser_AST.prange in
               let uu____2541 = aux loc env1 app in
               (match uu____2541 with
                | (env2,e,b,p2,uu____2558) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2574 =
                            let uu____2575 =
                              let uu____2582 =
                                let uu___228_2583 = fv in
                                let uu____2584 =
                                  let uu____2586 =
                                    let uu____2587 =
                                      let uu____2591 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2591) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2587 in
                                  FStar_Pervasives_Native.Some uu____2586 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___228_2583.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___228_2583.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2584
                                } in
                              (uu____2582, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2575 in
                          FStar_All.pipe_left pos uu____2574
                      | uu____2605 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2634 = aux loc env1 p2 in
               (match uu____2634 with
                | (loc1,env2,var,p3,uu____2650) ->
                    let uu____2653 =
                      FStar_List.fold_left
                        (fun uu____2675  ->
                           fun p4  ->
                             match uu____2675 with
                             | (loc2,env3,ps1) ->
                                 let uu____2694 = aux loc2 env3 p4 in
                                 (match uu____2694 with
                                  | (loc3,env4,uu____2708,p5,uu____2710) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2653 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2738 ->
               let uu____2739 = aux loc env1 p1 in
               (match uu____2739 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2762 = aux_maybe_or env p in
         match uu____2762 with
         | (env1,b,pats) ->
             ((let uu____2780 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2780);
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
            let uu____2802 =
              let uu____2803 =
                let uu____2806 = FStar_ToSyntax_Env.qualify env x in
                (uu____2806, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2803 in
            (env, uu____2802, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2817 =
                  let uu____2818 =
                    let uu____2821 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2821, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2818 in
                mklet uu____2817
            | FStar_Parser_AST.PatVar (x,uu____2823) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2827);
                   FStar_Parser_AST.prange = uu____2828;_},t)
                ->
                let uu____2832 =
                  let uu____2833 =
                    let uu____2836 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2837 = desugar_term env t in
                    (uu____2836, uu____2837) in
                  LetBinder uu____2833 in
                (env, uu____2832, [])
            | uu____2839 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2845 = desugar_data_pat env p is_mut in
             match uu____2845 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2862;
                       FStar_Syntax_Syntax.p = uu____2863;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2866;
                       FStar_Syntax_Syntax.p = uu____2867;_}::[] -> []
                   | uu____2870 -> p1 in
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
  fun uu____2875  ->
    fun env  ->
      fun pat  ->
        let uu____2878 = desugar_data_pat env pat false in
        match uu____2878 with | (env1,uu____2887,pat1) -> (env1, pat1)
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
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2902  ->
        fun range  ->
          match uu____2902 with
          | (signedness,width) ->
              let uu____2910 = FStar_Const.bounds signedness width in
              (match uu____2910 with
               | (lower,upper) ->
                   let value =
                     let uu____2918 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2918 in
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
                      (let uu____2921 =
                         let uu____2922 =
                           let uu____2925 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2925, range) in
                         FStar_Errors.Error uu____2922 in
                       raise uu____2921)
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
                       let uu____2933 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2933 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____2940)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2948 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2948 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___229_2949 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___229_2949.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___229_2949.FStar_Syntax_Syntax.pos)
                                }
                            | uu____2952 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____2957 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2957 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____2972 =
                       let uu____2975 =
                         let uu____2976 =
                           let uu____2986 =
                             let uu____2992 =
                               let uu____2997 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2997) in
                             [uu____2992] in
                           (lid1, uu____2986) in
                         FStar_Syntax_Syntax.Tm_app uu____2976 in
                       FStar_Syntax_Syntax.mk uu____2975 in
                     uu____2972 FStar_Pervasives_Native.None range)))
and desugar_name:
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____3034 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3034 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3045 =
                    let uu____3046 =
                      let uu____3051 = mk_ref_read tm1 in
                      (uu____3051,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3046 in
                  FStar_All.pipe_left mk1 uu____3045
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3065 =
          let uu____3066 = unparen t in uu____3066.FStar_Parser_AST.tm in
        match uu____3065 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3067; FStar_Ident.ident = uu____3068;
              FStar_Ident.nsstr = uu____3069; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3071 ->
            let uu____3072 =
              let uu____3073 =
                let uu____3076 =
                  let uu____3077 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3077 in
                (uu____3076, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3073 in
            raise uu____3072 in
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
          let uu___230_3101 = e in
          {
            FStar_Syntax_Syntax.n = (uu___230_3101.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___230_3101.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range)
          } in
        let uu____3106 =
          let uu____3107 = unparen top in uu____3107.FStar_Parser_AST.tm in
        match uu____3106 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3108 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3140::uu____3141::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3144 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3144 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3153;_},t1::t2::[])
                  ->
                  let uu____3157 = flatten1 t1 in
                  FStar_List.append uu____3157 [t2]
              | uu____3159 -> [t] in
            let targs =
              let uu____3162 =
                let uu____3164 = unparen top in flatten1 uu____3164 in
              FStar_All.pipe_right uu____3162
                (FStar_List.map
                   (fun t  ->
                      let uu____3170 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3170)) in
            let uu____3171 =
              let uu____3174 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3174 in
            (match uu____3171 with
             | (tup,uu____3184) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3187 =
              let uu____3190 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____3190 in
            FStar_All.pipe_left setpos uu____3187
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3204 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3204 with
             | FStar_Pervasives_Native.None  ->
                 raise
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
                             let uu____3233 = desugar_term env t in
                             (uu____3233, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3242)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3250 =
              let uu___231_3251 = top in
              let uu____3252 =
                let uu____3253 =
                  let uu____3257 =
                    let uu___232_3258 = top in
                    let uu____3259 =
                      let uu____3260 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3260 in
                    {
                      FStar_Parser_AST.tm = uu____3259;
                      FStar_Parser_AST.range =
                        (uu___232_3258.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3258.FStar_Parser_AST.level)
                    } in
                  (uu____3257, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3253 in
              {
                FStar_Parser_AST.tm = uu____3252;
                FStar_Parser_AST.range =
                  (uu___231_3251.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3251.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3250
        | FStar_Parser_AST.Construct (n1,(a,uu____3263)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3271 =
              let uu___233_3272 = top in
              let uu____3273 =
                let uu____3274 =
                  let uu____3278 =
                    let uu___234_3279 = top in
                    let uu____3280 =
                      let uu____3281 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3281 in
                    {
                      FStar_Parser_AST.tm = uu____3280;
                      FStar_Parser_AST.range =
                        (uu___234_3279.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3279.FStar_Parser_AST.level)
                    } in
                  (uu____3278, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3274 in
              {
                FStar_Parser_AST.tm = uu____3273;
                FStar_Parser_AST.range =
                  (uu___233_3272.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3272.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3271
        | FStar_Parser_AST.Construct (n1,(a,uu____3284)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3292 =
              let uu___235_3293 = top in
              let uu____3294 =
                let uu____3295 =
                  let uu____3299 =
                    let uu___236_3300 = top in
                    let uu____3301 =
                      let uu____3302 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3302 in
                    {
                      FStar_Parser_AST.tm = uu____3301;
                      FStar_Parser_AST.range =
                        (uu___236_3300.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___236_3300.FStar_Parser_AST.level)
                    } in
                  (uu____3299, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3295 in
              {
                FStar_Parser_AST.tm = uu____3294;
                FStar_Parser_AST.range =
                  (uu___235_3293.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___235_3293.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3292
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3303; FStar_Ident.ident = uu____3304;
              FStar_Ident.nsstr = uu____3305; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3307; FStar_Ident.ident = uu____3308;
              FStar_Ident.nsstr = uu____3309; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3311; FStar_Ident.ident = uu____3312;
               FStar_Ident.nsstr = uu____3313; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3323 =
              let uu____3324 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3324 in
            mk1 uu____3323
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3325; FStar_Ident.ident = uu____3326;
              FStar_Ident.nsstr = uu____3327; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3329; FStar_Ident.ident = uu____3330;
              FStar_Ident.nsstr = uu____3331; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3333; FStar_Ident.ident = uu____3334;
              FStar_Ident.nsstr = uu____3335; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3339;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3341 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3341 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____3345 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3345))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3349 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3349 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    raise
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
                let uu____3369 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3369 with
                | FStar_Pervasives_Native.Some uu____3374 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____3377 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3377 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____3385 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____3393 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3393
              | uu____3394 ->
                  let uu____3398 =
                    let uu____3399 =
                      let uu____3402 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3402, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3399 in
                  raise uu____3398))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3405 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3405 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3407 =
                    let uu____3408 =
                      let uu____3411 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3411, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3408 in
                  raise uu____3407
              | uu____3412 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3424 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3424 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____3427 =
                    let uu____3432 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3432, true) in
                  (match uu____3427 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3445 ->
                            let uu____3449 =
                              FStar_Util.take
                                (fun uu____3463  ->
                                   match uu____3463 with
                                   | (uu____3466,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3449 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3504  ->
                                        match uu____3504 with
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
                    let uu____3536 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3536 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____3538 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3543 =
              FStar_List.fold_left
                (fun uu____3572  ->
                   fun b  ->
                     match uu____3572 with
                     | (env1,tparams,typs) ->
                         let uu____3603 = desugar_binder env1 b in
                         (match uu____3603 with
                          | (xopt,t1) ->
                              let uu____3619 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____3624 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3624)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3619 with
                               | (env2,x) ->
                                   let uu____3636 =
                                     let uu____3638 =
                                       let uu____3640 =
                                         let uu____3641 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3641 in
                                       [uu____3640] in
                                     FStar_List.append typs uu____3638 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___237_3655 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___237_3655.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___237_3655.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____3636)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____3543 with
             | (env1,uu____3668,targs) ->
                 let uu____3680 =
                   let uu____3683 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3683 in
                 (match uu____3680 with
                  | (tup,uu____3693) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3701 = uncurry binders t in
            (match uu____3701 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___210_3724 =
                   match uu___210_3724 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3734 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3734
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3750 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3750 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3761 = desugar_binder env b in
            (match uu____3761 with
             | (FStar_Pervasives_Native.None ,uu____3765) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3771 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____3771 with
                  | ((x,uu____3775),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3780 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3780))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3795 =
              FStar_List.fold_left
                (fun uu____3809  ->
                   fun pat  ->
                     match uu____3809 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3824,t) ->
                              let uu____3826 =
                                let uu____3828 = free_type_vars env1 t in
                                FStar_List.append uu____3828 ftvs in
                              (env1, uu____3826)
                          | uu____3831 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3795 with
             | (uu____3834,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3842 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3842 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___211_3872 =
                   match uu___211_3872 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____3901 =
                                 let uu____3902 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3902
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3901 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____3940 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3940
                   | p::rest ->
                       let uu____3948 = desugar_binding_pat env1 p in
                       (match uu____3948 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____3964 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3967 =
                              match b with
                              | LetBinder uu____3986 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____4017) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____4040 =
                                          let uu____4043 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____4043, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____4040
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4068,uu____4069) ->
                                             let tup2 =
                                               let uu____4071 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4071
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4075 =
                                                 let uu____4078 =
                                                   let uu____4079 =
                                                     let uu____4089 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4092 =
                                                       let uu____4094 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4095 =
                                                         let uu____4097 =
                                                           let uu____4098 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4098 in
                                                         [uu____4097] in
                                                       uu____4094 ::
                                                         uu____4095 in
                                                     (uu____4089, uu____4092) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4079 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4078 in
                                               uu____4075
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4112 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____4112 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4130,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4132,pats)) ->
                                             let tupn =
                                               let uu____4157 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4157
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4169 =
                                                 let uu____4170 =
                                                   let uu____4180 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4183 =
                                                     let uu____4189 =
                                                       let uu____4195 =
                                                         let uu____4196 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4196 in
                                                       [uu____4195] in
                                                     FStar_List.append args
                                                       uu____4189 in
                                                   (uu____4180, uu____4183) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4170 in
                                               mk1 uu____4169 in
                                             let p2 =
                                               let uu____4210 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____4210 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____4230 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3967 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____4271,uu____4272,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4284 =
                let uu____4285 = unparen e in uu____4285.FStar_Parser_AST.tm in
              match uu____4284 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4291 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4295;
               FStar_Parser_AST.level = uu____4296;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Parser_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4299 =
                let uu____4300 = unparen top in
                uu____4300.FStar_Parser_AST.tm in
              match uu____4299 with
              | FStar_Parser_AST.App (l,uu____4302,uu____4303) -> l
              | uu____4304 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____4306 =
                let uu____4307 =
                  let uu____4311 =
                    let uu____4312 =
                      let uu____4313 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4313 in
                    FStar_Parser_AST.mk_term uu____4312
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____4314 =
                    let uu____4315 =
                      let uu____4316 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4316 in
                    FStar_Parser_AST.mk_term uu____4315
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____4311, uu____4314, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4307 in
              FStar_Parser_AST.mk_term uu____4306 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type,
                             FStar_Pervasives_Native.None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term env t'
        | FStar_Parser_AST.App uu____4319 ->
            let rec aux args e =
              let uu____4340 =
                let uu____4341 = unparen e in uu____4341.FStar_Parser_AST.tm in
              match uu____4340 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4351 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4351 in
                  aux (arg :: args) e1
              | uu____4358 ->
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
              let uu____4375 =
                let uu____4376 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4376 in
              FStar_Parser_AST.mk_term uu____4375 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4377 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4377
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4380 =
              let uu____4381 =
                let uu____4386 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4386,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4381 in
            mk1 uu____4380
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4397 =
              let uu____4402 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4402 then desugar_typ else desugar_term in
            uu____4397 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4427 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4474  ->
                        match uu____4474 with
                        | (p,def) ->
                            let uu____4488 = is_app_pattern p in
                            if uu____4488
                            then
                              let uu____4498 =
                                destruct_app_pattern env top_level p in
                              (uu____4498, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____4527 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4527, def1)
                               | uu____4542 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4556);
                                           FStar_Parser_AST.prange =
                                             uu____4557;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4570 =
                                            let uu____4578 =
                                              let uu____4581 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4581 in
                                            (uu____4578, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____4570, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____4606)
                                        ->
                                        if top_level
                                        then
                                          let uu____4618 =
                                            let uu____4626 =
                                              let uu____4629 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4629 in
                                            (uu____4626, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____4618, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____4653 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4663 =
                FStar_List.fold_left
                  (fun uu____4700  ->
                     fun uu____4701  ->
                       match (uu____4700, uu____4701) with
                       | ((env1,fnames,rec_bindings),((f,uu____4745,uu____4746),uu____4747))
                           ->
                           let uu____4787 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4801 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4801 with
                                  | (env2,xx) ->
                                      let uu____4812 =
                                        let uu____4814 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4814 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4812))
                             | FStar_Util.Inr l ->
                                 let uu____4819 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4819, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4787 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4663 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4892 =
                    match uu____4892 with
                    | ((uu____4904,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____4930 = is_comp_type env1 t in
                                if uu____4930
                                then
                                  ((let uu____4932 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4939 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4939)) in
                                    match uu____4932 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4942 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4944 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4944))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4942
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4951 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____4951 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4954 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4964 =
                                let uu____4965 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4965
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____4964 in
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
                  let uu____4985 =
                    let uu____4986 =
                      let uu____4994 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4994) in
                    FStar_Syntax_Syntax.Tm_let uu____4986 in
                  FStar_All.pipe_left mk1 uu____4985 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____5021 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____5021 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____5042 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____5042
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
                    | LocalBinder (x,uu____5050) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____5053;
                              FStar_Syntax_Syntax.p = uu____5054;_}::[] ->
                              body1
                          | uu____5057 ->
                              let uu____5059 =
                                let uu____5062 =
                                  let uu____5063 =
                                    let uu____5078 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____5079 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____5078, uu____5079) in
                                  FStar_Syntax_Syntax.Tm_match uu____5063 in
                                FStar_Syntax_Syntax.mk uu____5062 in
                              uu____5059 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____5092 =
                          let uu____5093 =
                            let uu____5101 =
                              let uu____5102 =
                                let uu____5103 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____5103] in
                              FStar_Syntax_Subst.close uu____5102 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5101) in
                          FStar_Syntax_Syntax.Tm_let uu____5093 in
                        FStar_All.pipe_left mk1 uu____5092 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5123 = is_rec || (is_app_pattern pat) in
            if uu____5123
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5132 =
                let uu____5133 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____5133 in
              mk1 uu____5132 in
            let uu____5134 =
              let uu____5135 =
                let uu____5150 =
                  let uu____5153 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5153
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____5171 =
                  let uu____5180 =
                    let uu____5188 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____5190 = desugar_term env t2 in
                    (uu____5188, FStar_Pervasives_Native.None, uu____5190) in
                  let uu____5197 =
                    let uu____5206 =
                      let uu____5214 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____5216 = desugar_term env t3 in
                      (uu____5214, FStar_Pervasives_Native.None, uu____5216) in
                    [uu____5206] in
                  uu____5180 :: uu____5197 in
                (uu____5150, uu____5171) in
              FStar_Syntax_Syntax.Tm_match uu____5135 in
            mk1 uu____5134
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
            let desugar_branch uu____5300 =
              match uu____5300 with
              | (pat,wopt,b) ->
                  let uu____5311 = desugar_match_pat env pat in
                  (match uu____5311 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____5324 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____5324 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5326 =
              let uu____5327 =
                let uu____5342 = desugar_term env e in
                let uu____5343 = FStar_List.collect desugar_branch branches in
                (uu____5342, uu____5343) in
              FStar_Syntax_Syntax.Tm_match uu____5327 in
            FStar_All.pipe_left mk1 uu____5326
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5362 = is_comp_type env t in
              if uu____5362
              then
                let uu____5367 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5367
              else
                (let uu____5373 = desugar_term env t in
                 FStar_Util.Inl uu____5373) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5378 =
              let uu____5379 =
                let uu____5397 = desugar_term env e in
                (uu____5397, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5379 in
            FStar_All.pipe_left mk1 uu____5378
        | FStar_Parser_AST.Record (uu____5413,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5434 = FStar_List.hd fields in
              match uu____5434 with | (f,uu____5441) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5468  ->
                        match uu____5468 with
                        | (g,uu____5472) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____5476,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____5484 =
                         let uu____5485 =
                           let uu____5488 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5488, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5485 in
                       raise uu____5484
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
                  let uu____5494 =
                    let uu____5500 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5518  ->
                              match uu____5518 with
                              | (f,uu____5524) ->
                                  let uu____5525 =
                                    let uu____5526 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____5526 in
                                  (uu____5525, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5500) in
                  FStar_Parser_AST.Construct uu____5494
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5537 =
                      let uu____5538 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5538 in
                    FStar_Parser_AST.mk_term uu____5537 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5540 =
                      let uu____5547 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5564  ->
                                match uu____5564 with
                                | (f,uu____5570) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____5547) in
                    FStar_Parser_AST.Record uu____5540 in
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
                         FStar_Syntax_Syntax.tk = uu____5586;
                         FStar_Syntax_Syntax.pos = uu____5587;_},args);
                    FStar_Syntax_Syntax.tk = uu____5589;
                    FStar_Syntax_Syntax.pos = uu____5590;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5610 =
                     let uu____5611 =
                       let uu____5621 =
                         let uu____5622 =
                           let uu____5624 =
                             let uu____5625 =
                               let uu____5629 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5629) in
                             FStar_Syntax_Syntax.Record_ctor uu____5625 in
                           FStar_Pervasives_Native.Some uu____5624 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5622 in
                       (uu____5621, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5611 in
                   FStar_All.pipe_left mk1 uu____5610 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5649 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5653 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5653 with
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
                  let uu____5666 =
                    let uu____5667 =
                      let uu____5677 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5678 =
                        let uu____5680 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5680] in
                      (uu____5677, uu____5678) in
                    FStar_Syntax_Syntax.Tm_app uu____5667 in
                  FStar_All.pipe_left mk1 uu____5666))
        | FStar_Parser_AST.NamedTyp (uu____5684,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5687 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5688 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5689,uu____5690,uu____5691) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5698,uu____5699,uu____5700) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5707,uu____5708,uu____5709) ->
            failwith "Not implemented yet"
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
           (fun uu____5737  ->
              match uu____5737 with
              | (a,imp) ->
                  let uu____5745 = desugar_term env a in
                  arg_withimp_e imp uu____5745))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____5762 =
          match uu____5762 with
          | (t1,uu____5766) ->
              let uu____5767 =
                let uu____5768 = unparen t1 in uu____5768.FStar_Parser_AST.tm in
              (match uu____5767 with
               | FStar_Parser_AST.Requires uu____5769 -> true
               | uu____5773 -> false) in
        let is_ensures uu____5779 =
          match uu____5779 with
          | (t1,uu____5783) ->
              let uu____5784 =
                let uu____5785 = unparen t1 in uu____5785.FStar_Parser_AST.tm in
              (match uu____5784 with
               | FStar_Parser_AST.Ensures uu____5786 -> true
               | uu____5790 -> false) in
        let is_app head1 uu____5799 =
          match uu____5799 with
          | (t1,uu____5803) ->
              let uu____5804 =
                let uu____5805 = unparen t1 in uu____5805.FStar_Parser_AST.tm in
              (match uu____5804 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5807;
                      FStar_Parser_AST.level = uu____5808;_},uu____5809,uu____5810)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5811 -> false) in
        let is_smt_pat uu____5817 =
          match uu____5817 with
          | (t1,uu____5821) ->
              let uu____5822 =
                let uu____5823 = unparen t1 in uu____5823.FStar_Parser_AST.tm in
              (match uu____5822 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5826);
                             FStar_Parser_AST.range = uu____5827;
                             FStar_Parser_AST.level = uu____5828;_},uu____5829)::uu____5830::[])
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
                             FStar_Parser_AST.range = uu____5852;
                             FStar_Parser_AST.level = uu____5853;_},uu____5854)::uu____5855::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5869 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5887 = head_and_args t1 in
          match uu____5887 with
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
                   let args1 =
                     match args with
                     | [] ->
                         raise
                           (FStar_Errors.Error
                              ("Not enough arguments to 'Lemma'",
                                (t1.FStar_Parser_AST.range)))
                     | ens::[] -> [unit_tm; req_true; ens; nil_pat]
                     | ens::smtpat::[] when is_smt_pat smtpat ->
                         [unit_tm; req_true; ens; smtpat]
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         [unit_tm; req; ens; nil_pat]
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
                     | more -> unit_tm :: more in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____6104 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____6104, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6120 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6120
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6131 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6131
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
               | uu____6151 ->
                   let default_effect =
                     let uu____6153 = FStar_Options.ml_ish () in
                     if uu____6153
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6156 =
                           FStar_Options.warn_default_effects () in
                         if uu____6156
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6169 = pre_process_comp_typ t in
        match uu____6169 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6201 =
                  let uu____6202 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6202 in
                fail uu____6201)
             else ();
             (let is_universe uu____6209 =
                match uu____6209 with
                | (uu____6212,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6214 = FStar_Util.take is_universe args in
              match uu____6214 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6248  ->
                         match uu____6248 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6253 =
                    let uu____6261 = FStar_List.hd args1 in
                    let uu____6266 = FStar_List.tl args1 in
                    (uu____6261, uu____6266) in
                  (match uu____6253 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6297 =
                         let is_decrease uu____6320 =
                           match uu____6320 with
                           | (t1,uu____6327) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6335;
                                       FStar_Syntax_Syntax.pos = uu____6336;_},uu____6337::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____6358 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6297 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6430  ->
                                      match uu____6430 with
                                      | (t1,uu____6437) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6444,(arg,uu____6446)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6468 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6480 -> false in
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
                                           | uu____6581 -> pat in
                                         let uu____6582 =
                                           let uu____6589 =
                                             let uu____6596 =
                                               let uu____6602 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6602, aq) in
                                             [uu____6596] in
                                           ens :: uu____6589 in
                                         req :: uu____6582
                                     | uu____6634 -> rest2
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
        | uu____6650 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___238_6671 = t in
        {
          FStar_Syntax_Syntax.n = (uu___238_6671.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___238_6671.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___239_6700 = b in
             {
               FStar_Parser_AST.b = (uu___239_6700.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___239_6700.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___239_6700.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6736 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6736)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____6745 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6745 with
             | (env1,a1) ->
                 let a2 =
                   let uu___240_6753 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___240_6753.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___240_6753.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6766 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6775 =
                     let uu____6778 =
                       let uu____6779 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6779] in
                     no_annot_abs uu____6778 body2 in
                   FStar_All.pipe_left setpos uu____6775 in
                 let uu____6784 =
                   let uu____6785 =
                     let uu____6795 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____6796 =
                       let uu____6798 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6798] in
                     (uu____6795, uu____6796) in
                   FStar_Syntax_Syntax.Tm_app uu____6785 in
                 FStar_All.pipe_left mk1 uu____6784)
        | uu____6802 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6851 = q (rest, pats, body) in
              let uu____6855 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6851 uu____6855
                FStar_Parser_AST.Formula in
            let uu____6856 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6856 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6861 -> failwith "impossible" in
      let uu____6863 =
        let uu____6864 = unparen f in uu____6864.FStar_Parser_AST.tm in
      match uu____6863 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6871,uu____6872) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6878,uu____6879) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6898 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6898
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6921 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6921
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6948 -> desugar_term env f
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
      let uu____6952 =
        FStar_List.fold_left
          (fun uu____6976  ->
             fun b  ->
               match uu____6976 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___241_7005 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___241_7005.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___241_7005.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___241_7005.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____7015 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____7015 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___242_7027 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___242_7027.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___242_7027.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____7036 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6952 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____7083 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____7083)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7087 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____7087)
      | FStar_Parser_AST.TVariable x ->
          let uu____7090 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____7090)
      | FStar_Parser_AST.NoName t ->
          let uu____7101 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____7101)
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
               (fun uu___212_7127  ->
                  match uu___212_7127 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7128 -> false)) in
        let quals2 q =
          let uu____7136 =
            (let uu____7139 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7139) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7136
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____7149 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7149;
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
            let uu____7178 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7200  ->
                        match uu____7200 with
                        | (x,uu____7205) ->
                            let uu____7206 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7206 with
                             | (field_name,uu____7211) ->
                                 let only_decl =
                                   ((let uu____7215 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____7215)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7217 =
                                        let uu____7218 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7218.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7217) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7228 =
                                       FStar_List.filter
                                         (fun uu___213_7231  ->
                                            match uu___213_7231 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7232 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7228
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___214_7241  ->
                                             match uu___214_7241 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7242 -> false)) in
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
                                      let uu____7248 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7248
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7252 =
                                        let uu____7255 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____7255 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7252;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7257 =
                                        let uu____7258 =
                                          let uu____7262 =
                                            let uu____7264 =
                                              let uu____7265 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7265
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7264] in
                                          ((false, [lb]), uu____7262) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7258 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7257;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7178 FStar_List.flatten
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
            (lid,uu____7297,t,uu____7299,n1,uu____7301) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____7304 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7304 with
             | (formals,uu____7314) ->
                 (match formals with
                  | [] -> []
                  | uu____7328 ->
                      let filter_records uu___215_7336 =
                        match uu___215_7336 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7338,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7345 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____7347 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7347 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7354 = FStar_Util.first_N n1 formals in
                      (match uu____7354 with
                       | (uu____7366,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7380 -> []
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
                    let uu____7426 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7426
                    then
                      let uu____7428 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7428
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7431 =
                      let uu____7434 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____7434 in
                    let uu____7435 =
                      let uu____7438 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7438 in
                    let uu____7441 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7431;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7435;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7441
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
          let tycon_id uu___216_7477 =
            match uu___216_7477 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7479,uu____7480) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7486,uu____7487,uu____7488) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7494,uu____7495,uu____7496) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7512,uu____7513,uu____7514) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7538) ->
                let uu____7539 =
                  let uu____7540 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7540 in
                FStar_Parser_AST.mk_term uu____7539 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7542 =
                  let uu____7543 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7543 in
                FStar_Parser_AST.mk_term uu____7542 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7545) ->
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
              | uu____7566 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7572 =
                     let uu____7573 =
                       let uu____7577 = binder_to_term b in
                       (out, uu____7577, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7573 in
                   FStar_Parser_AST.mk_term uu____7572
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___217_7584 =
            match uu___217_7584 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7617  ->
                       match uu____7617 with
                       | (x,t,uu____7624) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____7628 =
                    let uu____7629 =
                      let uu____7630 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7630 in
                    FStar_Parser_AST.mk_term uu____7629
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7628 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7633 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7649  ->
                          match uu____7649 with
                          | (x,uu____7655,uu____7656) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])), uu____7633)
            | uu____7683 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___218_7705 =
            match uu___218_7705 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7719 = typars_of_binders _env binders in
                (match uu____7719 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____7747 =
                         let uu____7748 =
                           let uu____7749 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7749 in
                         FStar_Parser_AST.mk_term uu____7748
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7747 binders in
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
            | uu____7759 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7785 =
              FStar_List.fold_left
                (fun uu____7810  ->
                   fun uu____7811  ->
                     match (uu____7810, uu____7811) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7859 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7859 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7785 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____7920 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____7920
                | uu____7921 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7926 = desugar_abstract_tc quals env [] tc in
              (match uu____7926 with
               | (uu____7933,uu____7934,se,uu____7936) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7939,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7948 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7948
                           then quals1
                           else
                             ((let uu____7953 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7954 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7953 uu____7954);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7958 ->
                               let uu____7959 =
                                 let uu____7962 =
                                   let uu____7963 =
                                     let uu____7971 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7971) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7963 in
                                 FStar_Syntax_Syntax.mk uu____7962 in
                               uu____7959 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___243_7980 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_7980.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_7980.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_7980.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____7982 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7985 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7985
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7995 = typars_of_binders env binders in
              (match uu____7995 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____8015 =
                           FStar_Util.for_some
                             (fun uu___219_8017  ->
                                match uu___219_8017 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____8018 -> false) quals in
                         if uu____8015
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____8024 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___220_8027  ->
                               match uu___220_8027 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____8028 -> false)) in
                     if uu____8024
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____8035 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____8035
                     then
                       let uu____8037 =
                         let uu____8041 =
                           let uu____8042 = unparen t in
                           uu____8042.FStar_Parser_AST.tm in
                         match uu____8041 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____8054 =
                               match FStar_List.rev args with
                               | (last_arg,uu____8070)::args_rev ->
                                   let uu____8077 =
                                     let uu____8078 = unparen last_arg in
                                     uu____8078.FStar_Parser_AST.tm in
                                   (match uu____8077 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____8093 -> ([], args))
                               | uu____8098 -> ([], args) in
                             (match uu____8054 with
                              | (cattributes,args1) ->
                                  let uu____8119 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8119))
                         | uu____8125 -> (t, []) in
                       match uu____8037 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___221_8141  ->
                                     match uu___221_8141 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8142 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8150)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8163 = tycon_record_as_variant trec in
              (match uu____8163 with
               | (t,fs) ->
                   let uu____8173 =
                     let uu____8175 =
                       let uu____8176 =
                         let uu____8181 =
                           let uu____8183 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8183 in
                         (uu____8181, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8176 in
                     uu____8175 :: quals in
                   desugar_tycon env d uu____8173 [t])
          | uu____8186::uu____8187 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8275 = et in
                match uu____8275 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8389 ->
                         let trec = tc in
                         let uu____8402 = tycon_record_as_variant trec in
                         (match uu____8402 with
                          | (t,fs) ->
                              let uu____8433 =
                                let uu____8435 =
                                  let uu____8436 =
                                    let uu____8441 =
                                      let uu____8443 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8443 in
                                    (uu____8441, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8436 in
                                uu____8435 :: quals1 in
                              collect_tcs uu____8433 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8489 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8489 with
                          | (env2,uu____8520,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8598 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8598 with
                          | (env2,uu____8629,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8693 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8717 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8717 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___223_8983  ->
                             match uu___223_8983 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____9019,uu____9020);
                                    FStar_Syntax_Syntax.sigrng = uu____9021;
                                    FStar_Syntax_Syntax.sigquals = uu____9022;
                                    FStar_Syntax_Syntax.sigmeta = uu____9023;
                                    FStar_Syntax_Syntax.sigattrs = uu____9024;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____9057 =
                                     typars_of_binders env1 binders in
                                   match uu____9057 with
                                   | (env2,tpars1) ->
                                       let uu____9074 =
                                         push_tparams env2 tpars1 in
                                       (match uu____9074 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____9093 =
                                   let uu____9104 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____9104) in
                                 [uu____9093]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____9141);
                                    FStar_Syntax_Syntax.sigrng = uu____9142;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9144;
                                    FStar_Syntax_Syntax.sigattrs = uu____9145;_},constrs,tconstr,quals1)
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
                                 let uu____9198 = push_tparams env1 tpars in
                                 (match uu____9198 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9240  ->
                                             match uu____9240 with
                                             | (x,uu____9248) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9253 =
                                        let uu____9268 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9331  ->
                                                  match uu____9331 with
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
                                                        let uu____9364 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9364 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___222_9372
                                                                 ->
                                                                match uu___222_9372
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9379
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9386 =
                                                        let uu____9397 =
                                                          let uu____9398 =
                                                            let uu____9399 =
                                                              let uu____9407
                                                                =
                                                                let uu____9410
                                                                  =
                                                                  let uu____9413
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9413 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9410 in
                                                              (name, univs1,
                                                                uu____9407,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9399 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9398;
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
                                                          uu____9397) in
                                                      (name, uu____9386))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9268 in
                                      (match uu____9253 with
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
                             | uu____9538 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9607  ->
                             match uu____9607 with
                             | (name_doc,uu____9622,uu____9623) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9666  ->
                             match uu____9666 with
                             | (uu____9677,uu____9678,se) -> se)) in
                   let uu____9694 =
                     let uu____9698 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9698 rng in
                   (match uu____9694 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9736  ->
                                  match uu____9736 with
                                  | (uu____9748,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9781,tps,k,uu____9784,constrs)
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
                                  | uu____9802 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9815  ->
                                 match uu____9815 with
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
      let uu____9839 =
        FStar_List.fold_left
          (fun uu____9856  ->
             fun b  ->
               match uu____9856 with
               | (env1,binders1) ->
                   let uu____9868 = desugar_binder env1 b in
                   (match uu____9868 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____9878 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____9878 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9888 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9839 with
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
                let uu____9972 = desugar_binders monad_env eff_binders in
                match uu____9972 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9985 =
                        let uu____9986 =
                          let uu____9990 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____9990 in
                        FStar_List.length uu____9986 in
                      uu____9985 = (Prims.parse_int "1") in
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
                          (uu____10021,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____10023,uu____10024,uu____10025),uu____10026)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____10043 ->
                          failwith "Malformed effect member declaration." in
                    let uu____10044 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____10052 = name_of_eff_decl decl in
                           FStar_List.mem uu____10052 mandatory_members)
                        eff_decls in
                    (match uu____10044 with
                     | (mandatory_members_decls,actions) ->
                         let uu____10062 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____10081  ->
                                   fun decl  ->
                                     match uu____10081 with
                                     | (env2,out) ->
                                         let uu____10093 =
                                           desugar_decl env2 decl in
                                         (match uu____10093 with
                                          | (env3,ses) ->
                                              let uu____10101 =
                                                let uu____10103 =
                                                  FStar_List.hd ses in
                                                uu____10103 :: out in
                                              (env3, uu____10101)))
                                (env1, [])) in
                         (match uu____10062 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____10149,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10152,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____10153,
                                                                (def,uu____10155)::
                                                                (cps_type,uu____10157)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10158;
                                                             FStar_Parser_AST.level
                                                               = uu____10159;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10186 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10186 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10198 =
                                                   let uu____10199 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10200 =
                                                     let uu____10201 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10201 in
                                                   let uu____10204 =
                                                     let uu____10205 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10205 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10199;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10200;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10204
                                                   } in
                                                 (uu____10198, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10209,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10212,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10231 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10231 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10243 =
                                                   let uu____10244 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10245 =
                                                     let uu____10246 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10246 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10244;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10245;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____10243, doc1))
                                        | uu____10250 ->
                                            raise
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
                                let uu____10269 =
                                  let uu____10270 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10270 in
                                ([], uu____10269) in
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
                                    let uu____10282 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____10282) in
                                  let uu____10292 =
                                    let uu____10293 =
                                      let uu____10294 =
                                        let uu____10295 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____10295 in
                                      let uu____10300 = lookup "return" in
                                      let uu____10301 = lookup "bind" in
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
                                          uu____10294;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10300;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10301;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10293 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10292;
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
                                       (fun uu___224_10305  ->
                                          match uu___224_10305 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10306 -> true
                                          | uu____10307 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10313 =
                                     let uu____10314 =
                                       let uu____10315 = lookup "return_wp" in
                                       let uu____10316 = lookup "bind_wp" in
                                       let uu____10317 =
                                         lookup "if_then_else" in
                                       let uu____10318 = lookup "ite_wp" in
                                       let uu____10319 = lookup "stronger" in
                                       let uu____10320 = lookup "close_wp" in
                                       let uu____10321 = lookup "assert_p" in
                                       let uu____10322 = lookup "assume_p" in
                                       let uu____10323 = lookup "null_wp" in
                                       let uu____10324 = lookup "trivial" in
                                       let uu____10325 =
                                         if rr
                                         then
                                           let uu____10326 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____10326
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10335 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10337 =
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
                                           uu____10315;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10316;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10317;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10318;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10319;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10320;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10321;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10322;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10323;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10324;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10325;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10335;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10337;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10314 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10313;
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
                                        fun uu____10355  ->
                                          match uu____10355 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10364 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10364 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10366 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10366
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
                let uu____10391 = desugar_binders env1 eff_binders in
                match uu____10391 with
                | (env2,binders) ->
                    let uu____10402 =
                      let uu____10412 = head_and_args defn in
                      match uu____10412 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10437 ->
                                let uu____10438 =
                                  let uu____10439 =
                                    let uu____10442 =
                                      let uu____10443 =
                                        let uu____10444 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10444 " not found" in
                                      Prims.strcat "Effect " uu____10443 in
                                    (uu____10442,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10439 in
                                raise uu____10438 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10446 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10462)::args_rev ->
                                let uu____10469 =
                                  let uu____10470 = unparen last_arg in
                                  uu____10470.FStar_Parser_AST.tm in
                                (match uu____10469 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10485 -> ([], args))
                            | uu____10490 -> ([], args) in
                          (match uu____10446 with
                           | (cattributes,args1) ->
                               let uu____10517 = desugar_args env2 args1 in
                               let uu____10522 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10517, uu____10522)) in
                    (match uu____10402 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10556 =
                           match uu____10556 with
                           | (uu____10563,x) ->
                               let uu____10567 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10567 with
                                | (edb,x1) ->
                                    (if
                                       (FStar_List.length args) <>
                                         (FStar_List.length edb)
                                     then
                                       raise
                                         (FStar_Errors.Error
                                            ("Unexpected number of arguments to effect constructor",
                                              (defn.FStar_Parser_AST.range)))
                                     else ();
                                     (let s =
                                        FStar_Syntax_Util.subst_of_list edb
                                          args in
                                      let uu____10591 =
                                        let uu____10592 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10592 in
                                      ([], uu____10591)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10596 =
                             let uu____10597 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____10597 in
                           let uu____10603 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10604 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10605 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10606 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10607 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10608 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10609 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10610 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10611 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10612 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10613 =
                             let uu____10614 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____10614 in
                           let uu____10620 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10621 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10622 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10629 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10630 =
                                    let uu____10631 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____10631 in
                                  let uu____10637 =
                                    let uu____10638 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____10638 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10629;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10630;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10637
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10596;
                             FStar_Syntax_Syntax.ret_wp = uu____10603;
                             FStar_Syntax_Syntax.bind_wp = uu____10604;
                             FStar_Syntax_Syntax.if_then_else = uu____10605;
                             FStar_Syntax_Syntax.ite_wp = uu____10606;
                             FStar_Syntax_Syntax.stronger = uu____10607;
                             FStar_Syntax_Syntax.close_wp = uu____10608;
                             FStar_Syntax_Syntax.assert_p = uu____10609;
                             FStar_Syntax_Syntax.assume_p = uu____10610;
                             FStar_Syntax_Syntax.null_wp = uu____10611;
                             FStar_Syntax_Syntax.trivial = uu____10612;
                             FStar_Syntax_Syntax.repr = uu____10613;
                             FStar_Syntax_Syntax.return_repr = uu____10620;
                             FStar_Syntax_Syntax.bind_repr = uu____10621;
                             FStar_Syntax_Syntax.actions = uu____10622
                           } in
                         let se =
                           let for_free =
                             let uu____10646 =
                               let uu____10647 =
                                 let uu____10651 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____10651 in
                               FStar_List.length uu____10647 in
                             uu____10646 = (Prims.parse_int "1") in
                           let uu____10672 =
                             let uu____10674 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____10674 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10672;
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
                                       let uu____10692 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10692 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10694 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10694
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
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____10708 = desugar_decl_noattrs env d in
      match uu____10708 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          (FStar_List.iter
             (fun a  ->
                let uu____10722 = FStar_Syntax_Print.term_to_string a in
                FStar_Util.print1 "Desugared attribute: %s\n" uu____10722)
             attrs1;
           (let uu____10723 =
              FStar_List.map
                (fun sigelt  ->
                   let uu___244_10728 = sigelt in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___244_10728.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___244_10728.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___244_10728.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___244_10728.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs = attrs1
                   }) sigelts in
            (env1, uu____10723)))
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
      | FStar_Parser_AST.Fsdoc uu____10747 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10759 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10759, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10783  ->
                 match uu____10783 with | (x,uu____10788) -> x) tcs in
          let uu____10791 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____10791 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10806;
                    FStar_Parser_AST.prange = uu____10807;_},uu____10808)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10813;
                    FStar_Parser_AST.prange = uu____10814;_},uu____10815)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10823;
                         FStar_Parser_AST.prange = uu____10824;_},uu____10825);
                    FStar_Parser_AST.prange = uu____10826;_},uu____10827)::[]
                   -> false
               | (p,uu____10836)::[] ->
                   let uu____10841 = is_app_pattern p in
                   Prims.op_Negation uu____10841
               | uu____10842 -> false) in
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
            let uu____10853 =
              let uu____10854 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10854.FStar_Syntax_Syntax.n in
            (match uu____10853 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10860) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10881::uu____10882 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____10884 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___225_10894  ->
                               match uu___225_10894 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10896;
                                   FStar_Syntax_Syntax.lbunivs = uu____10897;
                                   FStar_Syntax_Syntax.lbtyp = uu____10898;
                                   FStar_Syntax_Syntax.lbeff = uu____10899;
                                   FStar_Syntax_Syntax.lbdef = uu____10900;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10907;
                                   FStar_Syntax_Syntax.lbtyp = uu____10908;
                                   FStar_Syntax_Syntax.lbeff = uu____10909;
                                   FStar_Syntax_Syntax.lbdef = uu____10910;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10918 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10927  ->
                             match uu____10927 with
                             | (uu____10930,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10918
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10938 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10938
                   then
                     let uu____10943 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___245_10953 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___246_10955 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___246_10955.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___246_10955.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___245_10953.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___245_10953.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___245_10953.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___245_10953.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____10943)
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
             | uu____10977 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10981 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10992 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10981 with
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
                       let uu___247_11008 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___247_11008.FStar_Parser_AST.prange)
                       }
                   | uu____11009 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___248_11014 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___248_11014.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___248_11014.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___248_11014.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____11033 id =
                   match uu____11033 with
                   | (env1,ses) ->
                       let main =
                         let uu____11046 =
                           let uu____11047 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____11047 in
                         FStar_Parser_AST.mk_term uu____11046
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
                       let uu____11075 = desugar_decl env1 id_decl in
                       (match uu____11075 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____11086 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____11086 FStar_Util.set_elements in
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
            let uu____11108 = close_fun env t in desugar_term env uu____11108 in
          let quals1 =
            let uu____11111 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____11111
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____11116 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____11116;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____11124 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____11124 with
           | (t,uu____11132) ->
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
            let uu____11157 =
              let uu____11161 = FStar_Syntax_Syntax.null_binder t in
              [uu____11161] in
            let uu____11162 =
              let uu____11165 =
                let uu____11166 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____11166 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____11165 in
            FStar_Syntax_Util.arrow uu____11157 uu____11162 in
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
            let uu____11210 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11210 with
            | FStar_Pervasives_Native.None  ->
                let uu____11212 =
                  let uu____11213 =
                    let uu____11216 =
                      let uu____11217 =
                        let uu____11218 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11218 " not found" in
                      Prims.strcat "Effect name " uu____11217 in
                    (uu____11216, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11213 in
                raise uu____11212
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11222 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11244 =
                  let uu____11249 =
                    let uu____11253 = desugar_term env t in ([], uu____11253) in
                  FStar_Pervasives_Native.Some uu____11249 in
                (uu____11244, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11271 =
                  let uu____11276 =
                    let uu____11280 = desugar_term env wp in
                    ([], uu____11280) in
                  FStar_Pervasives_Native.Some uu____11276 in
                let uu____11285 =
                  let uu____11290 =
                    let uu____11294 = desugar_term env t in ([], uu____11294) in
                  FStar_Pervasives_Native.Some uu____11290 in
                (uu____11271, uu____11285)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11308 =
                  let uu____11313 =
                    let uu____11317 = desugar_term env t in ([], uu____11317) in
                  FStar_Pervasives_Native.Some uu____11313 in
                (FStar_Pervasives_Native.None, uu____11308) in
          (match uu____11222 with
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
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____11377  ->
           fun d  ->
             match uu____11377 with
             | (env1,sigelts) ->
                 let uu____11389 = desugar_decl env1 d in
                 (match uu____11389 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
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
          | (FStar_Pervasives_Native.None ,uu____11434) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11437;
               FStar_Syntax_Syntax.exports = uu____11438;
               FStar_Syntax_Syntax.is_interface = uu____11439;_},FStar_Parser_AST.Module
             (current_lid,uu____11441)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____11446) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11448 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11468 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11468, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11478 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11478, mname, decls, false) in
        match uu____11448 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11496 = desugar_decls env2 decls in
            (match uu____11496 with
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
          let uu____11534 =
            (FStar_Options.interactive ()) &&
              (let uu____11536 =
                 let uu____11537 =
                   let uu____11538 = FStar_Options.file_list () in
                   FStar_List.hd uu____11538 in
                 FStar_Util.get_file_extension uu____11537 in
               uu____11536 = "fsti") in
          if uu____11534 then as_interface m else m in
        let uu____11541 = desugar_modul_common curmod env m1 in
        match uu____11541 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11551 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____11565 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____11565 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11576 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11576
            then
              let uu____11577 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11577
            else ());
           (let uu____11579 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11579, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____11592 =
        FStar_List.fold_left
          (fun uu____11606  ->
             fun m  ->
               match uu____11606 with
               | (env1,mods) ->
                   let uu____11618 = desugar_modul env1 m in
                   (match uu____11618 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11592 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11644 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11644 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11650 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11650
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env