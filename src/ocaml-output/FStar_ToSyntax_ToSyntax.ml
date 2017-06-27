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
                                    (uu___229_2949.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___229_2949.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2954 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____2959 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2959 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____2974 =
                       let uu____2977 =
                         let uu____2978 =
                           let uu____2988 =
                             let uu____2994 =
                               let uu____2999 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2999) in
                             [uu____2994] in
                           (lid1, uu____2988) in
                         FStar_Syntax_Syntax.Tm_app uu____2978 in
                       FStar_Syntax_Syntax.mk uu____2977 in
                     uu____2974 FStar_Pervasives_Native.None range)))
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
            let uu____3036 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3036 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3047 =
                    let uu____3048 =
                      let uu____3053 = mk_ref_read tm1 in
                      (uu____3053,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3048 in
                  FStar_All.pipe_left mk1 uu____3047
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3067 =
          let uu____3068 = unparen t in uu____3068.FStar_Parser_AST.tm in
        match uu____3067 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3069; FStar_Ident.ident = uu____3070;
              FStar_Ident.nsstr = uu____3071; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3073 ->
            let uu____3074 =
              let uu____3075 =
                let uu____3078 =
                  let uu____3079 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3079 in
                (uu____3078, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3075 in
            raise uu____3074 in
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
          let uu___230_3103 = e in
          {
            FStar_Syntax_Syntax.n = (uu___230_3103.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___230_3103.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___230_3103.FStar_Syntax_Syntax.vars)
          } in
        let uu____3110 =
          let uu____3111 = unparen top in uu____3111.FStar_Parser_AST.tm in
        match uu____3110 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3112 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3144::uu____3145::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3148 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3148 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3157;_},t1::t2::[])
                  ->
                  let uu____3161 = flatten1 t1 in
                  FStar_List.append uu____3161 [t2]
              | uu____3163 -> [t] in
            let targs =
              let uu____3166 =
                let uu____3168 = unparen top in flatten1 uu____3168 in
              FStar_All.pipe_right uu____3166
                (FStar_List.map
                   (fun t  ->
                      let uu____3174 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3174)) in
            let uu____3175 =
              let uu____3178 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3178 in
            (match uu____3175 with
             | (tup,uu____3188) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3191 =
              let uu____3194 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____3194 in
            FStar_All.pipe_left setpos uu____3191
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3208 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3208 with
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
                             let uu____3237 = desugar_term env t in
                             (uu____3237, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3246)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3254 =
              let uu___231_3255 = top in
              let uu____3256 =
                let uu____3257 =
                  let uu____3261 =
                    let uu___232_3262 = top in
                    let uu____3263 =
                      let uu____3264 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3264 in
                    {
                      FStar_Parser_AST.tm = uu____3263;
                      FStar_Parser_AST.range =
                        (uu___232_3262.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3262.FStar_Parser_AST.level)
                    } in
                  (uu____3261, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3257 in
              {
                FStar_Parser_AST.tm = uu____3256;
                FStar_Parser_AST.range =
                  (uu___231_3255.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3255.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3254
        | FStar_Parser_AST.Construct (n1,(a,uu____3267)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3275 =
              let uu___233_3276 = top in
              let uu____3277 =
                let uu____3278 =
                  let uu____3282 =
                    let uu___234_3283 = top in
                    let uu____3284 =
                      let uu____3285 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3285 in
                    {
                      FStar_Parser_AST.tm = uu____3284;
                      FStar_Parser_AST.range =
                        (uu___234_3283.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3283.FStar_Parser_AST.level)
                    } in
                  (uu____3282, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3278 in
              {
                FStar_Parser_AST.tm = uu____3277;
                FStar_Parser_AST.range =
                  (uu___233_3276.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3276.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3275
        | FStar_Parser_AST.Construct (n1,(a,uu____3288)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3296 =
              let uu___235_3297 = top in
              let uu____3298 =
                let uu____3299 =
                  let uu____3303 =
                    let uu___236_3304 = top in
                    let uu____3305 =
                      let uu____3306 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3306 in
                    {
                      FStar_Parser_AST.tm = uu____3305;
                      FStar_Parser_AST.range =
                        (uu___236_3304.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___236_3304.FStar_Parser_AST.level)
                    } in
                  (uu____3303, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3299 in
              {
                FStar_Parser_AST.tm = uu____3298;
                FStar_Parser_AST.range =
                  (uu___235_3297.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___235_3297.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3296
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3307; FStar_Ident.ident = uu____3308;
              FStar_Ident.nsstr = uu____3309; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3311; FStar_Ident.ident = uu____3312;
              FStar_Ident.nsstr = uu____3313; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3315; FStar_Ident.ident = uu____3316;
               FStar_Ident.nsstr = uu____3317; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3327 =
              let uu____3328 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3328 in
            mk1 uu____3327
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3329; FStar_Ident.ident = uu____3330;
              FStar_Ident.nsstr = uu____3331; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3333; FStar_Ident.ident = uu____3334;
              FStar_Ident.nsstr = uu____3335; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3337; FStar_Ident.ident = uu____3338;
              FStar_Ident.nsstr = uu____3339; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3343;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3345 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3345 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____3349 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3349))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3353 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3353 with
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
                let uu____3373 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3373 with
                | FStar_Pervasives_Native.Some uu____3378 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____3381 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3381 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____3389 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____3397 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3397
              | uu____3398 ->
                  let uu____3402 =
                    let uu____3403 =
                      let uu____3406 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3406, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3403 in
                  raise uu____3402))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3409 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3409 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3411 =
                    let uu____3412 =
                      let uu____3415 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3415, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3412 in
                  raise uu____3411
              | uu____3416 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3428 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3428 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____3431 =
                    let uu____3436 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3436, true) in
                  (match uu____3431 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3449 ->
                            let uu____3453 =
                              FStar_Util.take
                                (fun uu____3467  ->
                                   match uu____3467 with
                                   | (uu____3470,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3453 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3508  ->
                                        match uu____3508 with
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
                    let uu____3540 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3540 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____3542 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3547 =
              FStar_List.fold_left
                (fun uu____3576  ->
                   fun b  ->
                     match uu____3576 with
                     | (env1,tparams,typs) ->
                         let uu____3607 = desugar_binder env1 b in
                         (match uu____3607 with
                          | (xopt,t1) ->
                              let uu____3623 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____3628 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3628)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3623 with
                               | (env2,x) ->
                                   let uu____3640 =
                                     let uu____3642 =
                                       let uu____3644 =
                                         let uu____3645 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3645 in
                                       [uu____3644] in
                                     FStar_List.append typs uu____3642 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___237_3659 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___237_3659.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___237_3659.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____3640)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____3547 with
             | (env1,uu____3672,targs) ->
                 let uu____3684 =
                   let uu____3687 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3687 in
                 (match uu____3684 with
                  | (tup,uu____3697) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3705 = uncurry binders t in
            (match uu____3705 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___210_3728 =
                   match uu___210_3728 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3738 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3738
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3754 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3754 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3765 = desugar_binder env b in
            (match uu____3765 with
             | (FStar_Pervasives_Native.None ,uu____3769) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3775 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____3775 with
                  | ((x,uu____3779),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3784 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3784))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3799 =
              FStar_List.fold_left
                (fun uu____3813  ->
                   fun pat  ->
                     match uu____3813 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3828,t) ->
                              let uu____3830 =
                                let uu____3832 = free_type_vars env1 t in
                                FStar_List.append uu____3832 ftvs in
                              (env1, uu____3830)
                          | uu____3835 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3799 with
             | (uu____3838,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3846 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3846 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___211_3876 =
                   match uu___211_3876 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____3905 =
                                 let uu____3906 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3906
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3905 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____3944 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3944
                   | p::rest ->
                       let uu____3952 = desugar_binding_pat env1 p in
                       (match uu____3952 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____3968 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3971 =
                              match b with
                              | LetBinder uu____3990 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____4021) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____4044 =
                                          let uu____4047 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____4047, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____4044
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4072,uu____4073) ->
                                             let tup2 =
                                               let uu____4075 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4075
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4079 =
                                                 let uu____4082 =
                                                   let uu____4083 =
                                                     let uu____4093 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4096 =
                                                       let uu____4098 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4099 =
                                                         let uu____4101 =
                                                           let uu____4102 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4102 in
                                                         [uu____4101] in
                                                       uu____4098 ::
                                                         uu____4099 in
                                                     (uu____4093, uu____4096) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4083 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4082 in
                                               uu____4079
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4116 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____4116 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4134,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4136,pats)) ->
                                             let tupn =
                                               let uu____4161 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4161
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4173 =
                                                 let uu____4174 =
                                                   let uu____4184 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4187 =
                                                     let uu____4193 =
                                                       let uu____4199 =
                                                         let uu____4200 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4200 in
                                                       [uu____4199] in
                                                     FStar_List.append args
                                                       uu____4193 in
                                                   (uu____4184, uu____4187) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4174 in
                                               mk1 uu____4173 in
                                             let p2 =
                                               let uu____4214 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____4214 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____4234 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3971 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____4275,uu____4276,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4288 =
                let uu____4289 = unparen e in uu____4289.FStar_Parser_AST.tm in
              match uu____4288 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4295 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4299;
               FStar_Parser_AST.level = uu____4300;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Parser_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4303 =
                let uu____4304 = unparen top in
                uu____4304.FStar_Parser_AST.tm in
              match uu____4303 with
              | FStar_Parser_AST.App (l,uu____4306,uu____4307) -> l
              | uu____4308 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____4310 =
                let uu____4311 =
                  let uu____4315 =
                    let uu____4316 =
                      let uu____4317 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4317 in
                    FStar_Parser_AST.mk_term uu____4316
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____4318 =
                    let uu____4319 =
                      let uu____4320 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4320 in
                    FStar_Parser_AST.mk_term uu____4319
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____4315, uu____4318, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4311 in
              FStar_Parser_AST.mk_term uu____4310 tau.FStar_Parser_AST.range
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
        | FStar_Parser_AST.App uu____4323 ->
            let rec aux args e =
              let uu____4344 =
                let uu____4345 = unparen e in uu____4345.FStar_Parser_AST.tm in
              match uu____4344 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4355 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4355 in
                  aux (arg :: args) e1
              | uu____4362 ->
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
              let uu____4379 =
                let uu____4380 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4380 in
              FStar_Parser_AST.mk_term uu____4379 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4381 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4381
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4384 =
              let uu____4385 =
                let uu____4390 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4390,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4385 in
            mk1 uu____4384
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4401 =
              let uu____4406 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4406 then desugar_typ else desugar_term in
            uu____4401 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4431 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4478  ->
                        match uu____4478 with
                        | (p,def) ->
                            let uu____4492 = is_app_pattern p in
                            if uu____4492
                            then
                              let uu____4502 =
                                destruct_app_pattern env top_level p in
                              (uu____4502, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____4531 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4531, def1)
                               | uu____4546 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4560);
                                           FStar_Parser_AST.prange =
                                             uu____4561;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4574 =
                                            let uu____4582 =
                                              let uu____4585 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4585 in
                                            (uu____4582, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____4574, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____4610)
                                        ->
                                        if top_level
                                        then
                                          let uu____4622 =
                                            let uu____4630 =
                                              let uu____4633 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4633 in
                                            (uu____4630, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____4622, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____4657 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4667 =
                FStar_List.fold_left
                  (fun uu____4704  ->
                     fun uu____4705  ->
                       match (uu____4704, uu____4705) with
                       | ((env1,fnames,rec_bindings),((f,uu____4749,uu____4750),uu____4751))
                           ->
                           let uu____4791 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4805 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4805 with
                                  | (env2,xx) ->
                                      let uu____4816 =
                                        let uu____4818 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4818 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4816))
                             | FStar_Util.Inr l ->
                                 let uu____4823 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4823, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4791 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4667 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4896 =
                    match uu____4896 with
                    | ((uu____4908,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____4934 = is_comp_type env1 t in
                                if uu____4934
                                then
                                  ((let uu____4936 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4943 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4943)) in
                                    match uu____4936 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4946 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4948 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4948))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4946
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4955 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____4955 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4958 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4968 =
                                let uu____4969 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4969
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____4968 in
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
                  let uu____4989 =
                    let uu____4990 =
                      let uu____4998 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4998) in
                    FStar_Syntax_Syntax.Tm_let uu____4990 in
                  FStar_All.pipe_left mk1 uu____4989 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____5025 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____5025 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____5046 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____5046
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
                    | LocalBinder (x,uu____5054) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____5057;
                              FStar_Syntax_Syntax.p = uu____5058;_}::[] ->
                              body1
                          | uu____5061 ->
                              let uu____5063 =
                                let uu____5066 =
                                  let uu____5067 =
                                    let uu____5082 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____5083 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____5082, uu____5083) in
                                  FStar_Syntax_Syntax.Tm_match uu____5067 in
                                FStar_Syntax_Syntax.mk uu____5066 in
                              uu____5063 FStar_Pervasives_Native.None
                                body1.FStar_Syntax_Syntax.pos in
                        let uu____5096 =
                          let uu____5097 =
                            let uu____5105 =
                              let uu____5106 =
                                let uu____5107 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____5107] in
                              FStar_Syntax_Subst.close uu____5106 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5105) in
                          FStar_Syntax_Syntax.Tm_let uu____5097 in
                        FStar_All.pipe_left mk1 uu____5096 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5127 = is_rec || (is_app_pattern pat) in
            if uu____5127
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5136 =
                let uu____5137 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____5137 in
              mk1 uu____5136 in
            let uu____5138 =
              let uu____5139 =
                let uu____5154 =
                  let uu____5157 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5157
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____5175 =
                  let uu____5184 =
                    let uu____5192 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____5194 = desugar_term env t2 in
                    (uu____5192, FStar_Pervasives_Native.None, uu____5194) in
                  let uu____5201 =
                    let uu____5210 =
                      let uu____5218 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____5220 = desugar_term env t3 in
                      (uu____5218, FStar_Pervasives_Native.None, uu____5220) in
                    [uu____5210] in
                  uu____5184 :: uu____5201 in
                (uu____5154, uu____5175) in
              FStar_Syntax_Syntax.Tm_match uu____5139 in
            mk1 uu____5138
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
            let desugar_branch uu____5304 =
              match uu____5304 with
              | (pat,wopt,b) ->
                  let uu____5315 = desugar_match_pat env pat in
                  (match uu____5315 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____5328 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____5328 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5330 =
              let uu____5331 =
                let uu____5346 = desugar_term env e in
                let uu____5347 = FStar_List.collect desugar_branch branches in
                (uu____5346, uu____5347) in
              FStar_Syntax_Syntax.Tm_match uu____5331 in
            FStar_All.pipe_left mk1 uu____5330
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5366 = is_comp_type env t in
              if uu____5366
              then
                let uu____5371 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5371
              else
                (let uu____5377 = desugar_term env t in
                 FStar_Util.Inl uu____5377) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5382 =
              let uu____5383 =
                let uu____5401 = desugar_term env e in
                (uu____5401, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5383 in
            FStar_All.pipe_left mk1 uu____5382
        | FStar_Parser_AST.Record (uu____5417,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5438 = FStar_List.hd fields in
              match uu____5438 with | (f,uu____5445) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5472  ->
                        match uu____5472 with
                        | (g,uu____5476) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____5480,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____5488 =
                         let uu____5489 =
                           let uu____5492 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5492, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5489 in
                       raise uu____5488
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
                  let uu____5498 =
                    let uu____5504 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5522  ->
                              match uu____5522 with
                              | (f,uu____5528) ->
                                  let uu____5529 =
                                    let uu____5530 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____5530 in
                                  (uu____5529, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5504) in
                  FStar_Parser_AST.Construct uu____5498
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5541 =
                      let uu____5542 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5542 in
                    FStar_Parser_AST.mk_term uu____5541 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5544 =
                      let uu____5551 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5568  ->
                                match uu____5568 with
                                | (f,uu____5574) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____5551) in
                    FStar_Parser_AST.Record uu____5544 in
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
                         FStar_Syntax_Syntax.tk = uu____5590;
                         FStar_Syntax_Syntax.pos = uu____5591;
                         FStar_Syntax_Syntax.vars = uu____5592;_},args);
                    FStar_Syntax_Syntax.tk = uu____5594;
                    FStar_Syntax_Syntax.pos = uu____5595;
                    FStar_Syntax_Syntax.vars = uu____5596;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5618 =
                     let uu____5619 =
                       let uu____5629 =
                         let uu____5630 =
                           let uu____5632 =
                             let uu____5633 =
                               let uu____5637 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5637) in
                             FStar_Syntax_Syntax.Record_ctor uu____5633 in
                           FStar_Pervasives_Native.Some uu____5632 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5630 in
                       (uu____5629, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5619 in
                   FStar_All.pipe_left mk1 uu____5618 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5657 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5661 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5661 with
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
                  let uu____5674 =
                    let uu____5675 =
                      let uu____5685 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5686 =
                        let uu____5688 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5688] in
                      (uu____5685, uu____5686) in
                    FStar_Syntax_Syntax.Tm_app uu____5675 in
                  FStar_All.pipe_left mk1 uu____5674))
        | FStar_Parser_AST.NamedTyp (uu____5692,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5695 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5696 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5697,uu____5698,uu____5699) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5706,uu____5707,uu____5708) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5715,uu____5716,uu____5717) ->
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
           (fun uu____5745  ->
              match uu____5745 with
              | (a,imp) ->
                  let uu____5753 = desugar_term env a in
                  arg_withimp_e imp uu____5753))
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
        let is_requires uu____5770 =
          match uu____5770 with
          | (t1,uu____5774) ->
              let uu____5775 =
                let uu____5776 = unparen t1 in uu____5776.FStar_Parser_AST.tm in
              (match uu____5775 with
               | FStar_Parser_AST.Requires uu____5777 -> true
               | uu____5781 -> false) in
        let is_ensures uu____5787 =
          match uu____5787 with
          | (t1,uu____5791) ->
              let uu____5792 =
                let uu____5793 = unparen t1 in uu____5793.FStar_Parser_AST.tm in
              (match uu____5792 with
               | FStar_Parser_AST.Ensures uu____5794 -> true
               | uu____5798 -> false) in
        let is_app head1 uu____5807 =
          match uu____5807 with
          | (t1,uu____5811) ->
              let uu____5812 =
                let uu____5813 = unparen t1 in uu____5813.FStar_Parser_AST.tm in
              (match uu____5812 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5815;
                      FStar_Parser_AST.level = uu____5816;_},uu____5817,uu____5818)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5819 -> false) in
        let is_smt_pat uu____5825 =
          match uu____5825 with
          | (t1,uu____5829) ->
              let uu____5830 =
                let uu____5831 = unparen t1 in uu____5831.FStar_Parser_AST.tm in
              (match uu____5830 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5834);
                             FStar_Parser_AST.range = uu____5835;
                             FStar_Parser_AST.level = uu____5836;_},uu____5837)::uu____5838::[])
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
                             FStar_Parser_AST.range = uu____5860;
                             FStar_Parser_AST.level = uu____5861;_},uu____5862)::uu____5863::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5877 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5895 = head_and_args t1 in
          match uu____5895 with
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
                   let uu____6112 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____6112, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6128 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6128
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6139 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6139
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
               | uu____6159 ->
                   let default_effect =
                     let uu____6161 = FStar_Options.ml_ish () in
                     if uu____6161
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6164 =
                           FStar_Options.warn_default_effects () in
                         if uu____6164
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6177 = pre_process_comp_typ t in
        match uu____6177 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6209 =
                  let uu____6210 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6210 in
                fail uu____6209)
             else ();
             (let is_universe uu____6217 =
                match uu____6217 with
                | (uu____6220,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6222 = FStar_Util.take is_universe args in
              match uu____6222 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6256  ->
                         match uu____6256 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6261 =
                    let uu____6269 = FStar_List.hd args1 in
                    let uu____6274 = FStar_List.tl args1 in
                    (uu____6269, uu____6274) in
                  (match uu____6261 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6305 =
                         let is_decrease uu____6328 =
                           match uu____6328 with
                           | (t1,uu____6335) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6343;
                                       FStar_Syntax_Syntax.pos = uu____6344;
                                       FStar_Syntax_Syntax.vars = uu____6345;_},uu____6346::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____6368 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6305 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6440  ->
                                      match uu____6440 with
                                      | (t1,uu____6447) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6454,(arg,uu____6456)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6478 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6490 -> false in
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
                                           | uu____6591 -> pat in
                                         let uu____6592 =
                                           let uu____6599 =
                                             let uu____6606 =
                                               let uu____6612 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6612, aq) in
                                             [uu____6606] in
                                           ens :: uu____6599 in
                                         req :: uu____6592
                                     | uu____6644 -> rest2
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
        | uu____6660 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___238_6681 = t in
        {
          FStar_Syntax_Syntax.n = (uu___238_6681.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___238_6681.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___238_6681.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___239_6712 = b in
             {
               FStar_Parser_AST.b = (uu___239_6712.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___239_6712.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___239_6712.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6748 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6748)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____6757 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6757 with
             | (env1,a1) ->
                 let a2 =
                   let uu___240_6765 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___240_6765.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___240_6765.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6778 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6787 =
                     let uu____6790 =
                       let uu____6791 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6791] in
                     no_annot_abs uu____6790 body2 in
                   FStar_All.pipe_left setpos uu____6787 in
                 let uu____6796 =
                   let uu____6797 =
                     let uu____6807 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____6808 =
                       let uu____6810 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6810] in
                     (uu____6807, uu____6808) in
                   FStar_Syntax_Syntax.Tm_app uu____6797 in
                 FStar_All.pipe_left mk1 uu____6796)
        | uu____6814 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6863 = q (rest, pats, body) in
              let uu____6867 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6863 uu____6867
                FStar_Parser_AST.Formula in
            let uu____6868 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6868 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6873 -> failwith "impossible" in
      let uu____6875 =
        let uu____6876 = unparen f in uu____6876.FStar_Parser_AST.tm in
      match uu____6875 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6883,uu____6884) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6890,uu____6891) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6910 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6910
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6933 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6933
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6960 -> desugar_term env f
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
      let uu____6964 =
        FStar_List.fold_left
          (fun uu____6988  ->
             fun b  ->
               match uu____6988 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___241_7017 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___241_7017.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___241_7017.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___241_7017.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____7027 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____7027 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___242_7039 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___242_7039.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___242_7039.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____7048 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6964 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____7095 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____7095)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7099 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____7099)
      | FStar_Parser_AST.TVariable x ->
          let uu____7102 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____7102)
      | FStar_Parser_AST.NoName t ->
          let uu____7113 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____7113)
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
               (fun uu___212_7139  ->
                  match uu___212_7139 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7140 -> false)) in
        let quals2 q =
          let uu____7148 =
            (let uu____7151 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7151) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7148
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____7161 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7161;
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
            let uu____7190 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7212  ->
                        match uu____7212 with
                        | (x,uu____7217) ->
                            let uu____7218 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7218 with
                             | (field_name,uu____7223) ->
                                 let only_decl =
                                   ((let uu____7227 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____7227)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7229 =
                                        let uu____7230 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7230.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7229) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7240 =
                                       FStar_List.filter
                                         (fun uu___213_7243  ->
                                            match uu___213_7243 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7244 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7240
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___214_7253  ->
                                             match uu___214_7253 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7254 -> false)) in
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
                                      let uu____7260 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7260
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7264 =
                                        let uu____7267 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____7267 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7264;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7269 =
                                        let uu____7270 =
                                          let uu____7274 =
                                            let uu____7276 =
                                              let uu____7277 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7277
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7276] in
                                          ((false, [lb]), uu____7274) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7270 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7269;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7190 FStar_List.flatten
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
            (lid,uu____7309,t,uu____7311,n1,uu____7313) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____7316 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7316 with
             | (formals,uu____7326) ->
                 (match formals with
                  | [] -> []
                  | uu____7340 ->
                      let filter_records uu___215_7348 =
                        match uu___215_7348 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7350,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7357 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____7359 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7359 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7366 = FStar_Util.first_N n1 formals in
                      (match uu____7366 with
                       | (uu____7378,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7392 -> []
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
                    let uu____7438 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7438
                    then
                      let uu____7440 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7440
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7443 =
                      let uu____7446 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____7446 in
                    let uu____7447 =
                      let uu____7450 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7450 in
                    let uu____7453 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7443;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7447;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7453
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
          let tycon_id uu___216_7489 =
            match uu___216_7489 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7491,uu____7492) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7498,uu____7499,uu____7500) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7506,uu____7507,uu____7508) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7524,uu____7525,uu____7526) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7550) ->
                let uu____7551 =
                  let uu____7552 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7552 in
                FStar_Parser_AST.mk_term uu____7551 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7554 =
                  let uu____7555 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7555 in
                FStar_Parser_AST.mk_term uu____7554 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7557) ->
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
              | uu____7578 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7584 =
                     let uu____7585 =
                       let uu____7589 = binder_to_term b in
                       (out, uu____7589, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7585 in
                   FStar_Parser_AST.mk_term uu____7584
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___217_7596 =
            match uu___217_7596 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7629  ->
                       match uu____7629 with
                       | (x,t,uu____7636) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____7640 =
                    let uu____7641 =
                      let uu____7642 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7642 in
                    FStar_Parser_AST.mk_term uu____7641
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7640 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7645 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7661  ->
                          match uu____7661 with
                          | (x,uu____7667,uu____7668) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])), uu____7645)
            | uu____7695 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___218_7717 =
            match uu___218_7717 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7731 = typars_of_binders _env binders in
                (match uu____7731 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____7759 =
                         let uu____7760 =
                           let uu____7761 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7761 in
                         FStar_Parser_AST.mk_term uu____7760
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7759 binders in
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
            | uu____7771 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7797 =
              FStar_List.fold_left
                (fun uu____7822  ->
                   fun uu____7823  ->
                     match (uu____7822, uu____7823) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7871 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7871 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7797 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____7932 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____7932
                | uu____7933 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7938 = desugar_abstract_tc quals env [] tc in
              (match uu____7938 with
               | (uu____7945,uu____7946,se,uu____7948) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7951,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7960 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7960
                           then quals1
                           else
                             ((let uu____7965 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7966 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7965 uu____7966);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7970 ->
                               let uu____7971 =
                                 let uu____7974 =
                                   let uu____7975 =
                                     let uu____7983 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7983) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7975 in
                                 FStar_Syntax_Syntax.mk uu____7974 in
                               uu____7971 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___243_7992 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_7992.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_7992.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_7992.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____7994 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7997 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7997
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____8007 = typars_of_binders env binders in
              (match uu____8007 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____8027 =
                           FStar_Util.for_some
                             (fun uu___219_8029  ->
                                match uu___219_8029 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____8030 -> false) quals in
                         if uu____8027
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____8036 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___220_8039  ->
                               match uu___220_8039 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____8040 -> false)) in
                     if uu____8036
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____8047 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____8047
                     then
                       let uu____8049 =
                         let uu____8053 =
                           let uu____8054 = unparen t in
                           uu____8054.FStar_Parser_AST.tm in
                         match uu____8053 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____8066 =
                               match FStar_List.rev args with
                               | (last_arg,uu____8082)::args_rev ->
                                   let uu____8089 =
                                     let uu____8090 = unparen last_arg in
                                     uu____8090.FStar_Parser_AST.tm in
                                   (match uu____8089 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____8105 -> ([], args))
                               | uu____8110 -> ([], args) in
                             (match uu____8066 with
                              | (cattributes,args1) ->
                                  let uu____8131 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8131))
                         | uu____8137 -> (t, []) in
                       match uu____8049 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___221_8153  ->
                                     match uu___221_8153 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8154 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8162)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8175 = tycon_record_as_variant trec in
              (match uu____8175 with
               | (t,fs) ->
                   let uu____8185 =
                     let uu____8187 =
                       let uu____8188 =
                         let uu____8193 =
                           let uu____8195 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8195 in
                         (uu____8193, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8188 in
                     uu____8187 :: quals in
                   desugar_tycon env d uu____8185 [t])
          | uu____8198::uu____8199 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8287 = et in
                match uu____8287 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8401 ->
                         let trec = tc in
                         let uu____8414 = tycon_record_as_variant trec in
                         (match uu____8414 with
                          | (t,fs) ->
                              let uu____8445 =
                                let uu____8447 =
                                  let uu____8448 =
                                    let uu____8453 =
                                      let uu____8455 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8455 in
                                    (uu____8453, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8448 in
                                uu____8447 :: quals1 in
                              collect_tcs uu____8445 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8501 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8501 with
                          | (env2,uu____8532,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8610 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8610 with
                          | (env2,uu____8641,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8705 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8729 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8729 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___223_8995  ->
                             match uu___223_8995 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____9031,uu____9032);
                                    FStar_Syntax_Syntax.sigrng = uu____9033;
                                    FStar_Syntax_Syntax.sigquals = uu____9034;
                                    FStar_Syntax_Syntax.sigmeta = uu____9035;
                                    FStar_Syntax_Syntax.sigattrs = uu____9036;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____9069 =
                                     typars_of_binders env1 binders in
                                   match uu____9069 with
                                   | (env2,tpars1) ->
                                       let uu____9086 =
                                         push_tparams env2 tpars1 in
                                       (match uu____9086 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____9105 =
                                   let uu____9116 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____9116) in
                                 [uu____9105]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____9153);
                                    FStar_Syntax_Syntax.sigrng = uu____9154;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9156;
                                    FStar_Syntax_Syntax.sigattrs = uu____9157;_},constrs,tconstr,quals1)
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
                                 let uu____9210 = push_tparams env1 tpars in
                                 (match uu____9210 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9252  ->
                                             match uu____9252 with
                                             | (x,uu____9260) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9265 =
                                        let uu____9280 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9343  ->
                                                  match uu____9343 with
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
                                                        let uu____9376 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9376 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___222_9384
                                                                 ->
                                                                match uu___222_9384
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9391
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9398 =
                                                        let uu____9409 =
                                                          let uu____9410 =
                                                            let uu____9411 =
                                                              let uu____9419
                                                                =
                                                                let uu____9422
                                                                  =
                                                                  let uu____9425
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9425 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9422 in
                                                              (name, univs1,
                                                                uu____9419,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9411 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9410;
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
                                                          uu____9409) in
                                                      (name, uu____9398))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9280 in
                                      (match uu____9265 with
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
                             | uu____9550 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9619  ->
                             match uu____9619 with
                             | (name_doc,uu____9634,uu____9635) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9678  ->
                             match uu____9678 with
                             | (uu____9689,uu____9690,se) -> se)) in
                   let uu____9706 =
                     let uu____9710 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9710 rng in
                   (match uu____9706 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9748  ->
                                  match uu____9748 with
                                  | (uu____9760,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9793,tps,k,uu____9796,constrs)
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
                                  | uu____9814 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9827  ->
                                 match uu____9827 with
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
      let uu____9851 =
        FStar_List.fold_left
          (fun uu____9868  ->
             fun b  ->
               match uu____9868 with
               | (env1,binders1) ->
                   let uu____9880 = desugar_binder env1 b in
                   (match uu____9880 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____9890 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____9890 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9900 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9851 with
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
                let uu____9984 = desugar_binders monad_env eff_binders in
                match uu____9984 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9997 =
                        let uu____9998 =
                          let uu____10002 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____10002 in
                        FStar_List.length uu____9998 in
                      uu____9997 = (Prims.parse_int "1") in
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
                          (uu____10033,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____10035,uu____10036,uu____10037),uu____10038)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____10055 ->
                          failwith "Malformed effect member declaration." in
                    let uu____10056 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____10064 = name_of_eff_decl decl in
                           FStar_List.mem uu____10064 mandatory_members)
                        eff_decls in
                    (match uu____10056 with
                     | (mandatory_members_decls,actions) ->
                         let uu____10074 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____10093  ->
                                   fun decl  ->
                                     match uu____10093 with
                                     | (env2,out) ->
                                         let uu____10105 =
                                           desugar_decl env2 decl in
                                         (match uu____10105 with
                                          | (env3,ses) ->
                                              let uu____10113 =
                                                let uu____10115 =
                                                  FStar_List.hd ses in
                                                uu____10115 :: out in
                                              (env3, uu____10113)))
                                (env1, [])) in
                         (match uu____10074 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____10161,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10164,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____10165,
                                                                (def,uu____10167)::
                                                                (cps_type,uu____10169)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10170;
                                                             FStar_Parser_AST.level
                                                               = uu____10171;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10198 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10198 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10210 =
                                                   let uu____10211 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10212 =
                                                     let uu____10213 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10213 in
                                                   let uu____10216 =
                                                     let uu____10217 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10217 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10211;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10212;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10216
                                                   } in
                                                 (uu____10210, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10221,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10224,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10243 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10243 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10255 =
                                                   let uu____10256 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10257 =
                                                     let uu____10258 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10258 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10256;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10257;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____10255, doc1))
                                        | uu____10262 ->
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
                                let uu____10281 =
                                  let uu____10282 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10282 in
                                ([], uu____10281) in
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
                                    let uu____10294 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____10294) in
                                  let uu____10304 =
                                    let uu____10305 =
                                      let uu____10306 =
                                        let uu____10307 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____10307 in
                                      let uu____10312 = lookup "return" in
                                      let uu____10313 = lookup "bind" in
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
                                          uu____10306;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10312;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10313;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10305 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10304;
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
                                       (fun uu___224_10317  ->
                                          match uu___224_10317 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10318 -> true
                                          | uu____10319 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10325 =
                                     let uu____10326 =
                                       let uu____10327 = lookup "return_wp" in
                                       let uu____10328 = lookup "bind_wp" in
                                       let uu____10329 =
                                         lookup "if_then_else" in
                                       let uu____10330 = lookup "ite_wp" in
                                       let uu____10331 = lookup "stronger" in
                                       let uu____10332 = lookup "close_wp" in
                                       let uu____10333 = lookup "assert_p" in
                                       let uu____10334 = lookup "assume_p" in
                                       let uu____10335 = lookup "null_wp" in
                                       let uu____10336 = lookup "trivial" in
                                       let uu____10337 =
                                         if rr
                                         then
                                           let uu____10338 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____10338
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10347 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10349 =
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
                                           uu____10327;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10328;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10329;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10330;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10331;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10332;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10333;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10334;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10335;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10336;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10337;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10347;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10349;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10326 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10325;
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
                                        fun uu____10367  ->
                                          match uu____10367 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10376 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10376 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10378 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10378
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
                let uu____10403 = desugar_binders env1 eff_binders in
                match uu____10403 with
                | (env2,binders) ->
                    let uu____10414 =
                      let uu____10424 = head_and_args defn in
                      match uu____10424 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10449 ->
                                let uu____10450 =
                                  let uu____10451 =
                                    let uu____10454 =
                                      let uu____10455 =
                                        let uu____10456 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10456 " not found" in
                                      Prims.strcat "Effect " uu____10455 in
                                    (uu____10454,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10451 in
                                raise uu____10450 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10458 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10474)::args_rev ->
                                let uu____10481 =
                                  let uu____10482 = unparen last_arg in
                                  uu____10482.FStar_Parser_AST.tm in
                                (match uu____10481 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10497 -> ([], args))
                            | uu____10502 -> ([], args) in
                          (match uu____10458 with
                           | (cattributes,args1) ->
                               let uu____10529 = desugar_args env2 args1 in
                               let uu____10534 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10529, uu____10534)) in
                    (match uu____10414 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10568 =
                           match uu____10568 with
                           | (uu____10575,x) ->
                               let uu____10579 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10579 with
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
                                      let uu____10603 =
                                        let uu____10604 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10604 in
                                      ([], uu____10603)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10608 =
                             let uu____10609 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____10609 in
                           let uu____10615 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10616 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10617 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10618 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10619 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10620 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10621 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10622 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10623 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10624 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10625 =
                             let uu____10626 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____10626 in
                           let uu____10632 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10633 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10634 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10641 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10642 =
                                    let uu____10643 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____10643 in
                                  let uu____10649 =
                                    let uu____10650 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____10650 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10641;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10642;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10649
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10608;
                             FStar_Syntax_Syntax.ret_wp = uu____10615;
                             FStar_Syntax_Syntax.bind_wp = uu____10616;
                             FStar_Syntax_Syntax.if_then_else = uu____10617;
                             FStar_Syntax_Syntax.ite_wp = uu____10618;
                             FStar_Syntax_Syntax.stronger = uu____10619;
                             FStar_Syntax_Syntax.close_wp = uu____10620;
                             FStar_Syntax_Syntax.assert_p = uu____10621;
                             FStar_Syntax_Syntax.assume_p = uu____10622;
                             FStar_Syntax_Syntax.null_wp = uu____10623;
                             FStar_Syntax_Syntax.trivial = uu____10624;
                             FStar_Syntax_Syntax.repr = uu____10625;
                             FStar_Syntax_Syntax.return_repr = uu____10632;
                             FStar_Syntax_Syntax.bind_repr = uu____10633;
                             FStar_Syntax_Syntax.actions = uu____10634
                           } in
                         let se =
                           let for_free =
                             let uu____10658 =
                               let uu____10659 =
                                 let uu____10663 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____10663 in
                               FStar_List.length uu____10659 in
                             uu____10658 = (Prims.parse_int "1") in
                           let uu____10684 =
                             let uu____10686 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____10686 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10684;
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
                                       let uu____10704 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10704 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10706 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10706
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
      let uu____10720 = desugar_decl_noattrs env d in
      match uu____10720 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          (FStar_List.iter
             (fun a  ->
                let uu____10734 = FStar_Syntax_Print.term_to_string a in
                FStar_Util.print1 "Desugared attribute: %s\n" uu____10734)
             attrs1;
           (let uu____10735 =
              FStar_List.map
                (fun sigelt  ->
                   let uu___244_10740 = sigelt in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___244_10740.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___244_10740.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___244_10740.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___244_10740.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs = attrs1
                   }) sigelts in
            (env1, uu____10735)))
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
      | FStar_Parser_AST.Fsdoc uu____10759 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10771 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10771, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10795  ->
                 match uu____10795 with | (x,uu____10800) -> x) tcs in
          let uu____10803 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____10803 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10818;
                    FStar_Parser_AST.prange = uu____10819;_},uu____10820)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10825;
                    FStar_Parser_AST.prange = uu____10826;_},uu____10827)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10835;
                         FStar_Parser_AST.prange = uu____10836;_},uu____10837);
                    FStar_Parser_AST.prange = uu____10838;_},uu____10839)::[]
                   -> false
               | (p,uu____10848)::[] ->
                   let uu____10853 = is_app_pattern p in
                   Prims.op_Negation uu____10853
               | uu____10854 -> false) in
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
            let uu____10865 =
              let uu____10866 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10866.FStar_Syntax_Syntax.n in
            (match uu____10865 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10872) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10893::uu____10894 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____10896 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___225_10906  ->
                               match uu___225_10906 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10908;
                                   FStar_Syntax_Syntax.lbunivs = uu____10909;
                                   FStar_Syntax_Syntax.lbtyp = uu____10910;
                                   FStar_Syntax_Syntax.lbeff = uu____10911;
                                   FStar_Syntax_Syntax.lbdef = uu____10912;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10919;
                                   FStar_Syntax_Syntax.lbtyp = uu____10920;
                                   FStar_Syntax_Syntax.lbeff = uu____10921;
                                   FStar_Syntax_Syntax.lbdef = uu____10922;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10930 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10939  ->
                             match uu____10939 with
                             | (uu____10942,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10930
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10950 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10950
                   then
                     let uu____10955 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___245_10965 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___246_10967 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___246_10967.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___246_10967.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___245_10965.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___245_10965.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___245_10965.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___245_10965.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____10955)
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
             | uu____10989 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10993 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____11004 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10993 with
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
                       let uu___247_11020 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___247_11020.FStar_Parser_AST.prange)
                       }
                   | uu____11021 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___248_11026 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___248_11026.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___248_11026.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___248_11026.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____11045 id =
                   match uu____11045 with
                   | (env1,ses) ->
                       let main =
                         let uu____11058 =
                           let uu____11059 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____11059 in
                         FStar_Parser_AST.mk_term uu____11058
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
                       let uu____11087 = desugar_decl env1 id_decl in
                       (match uu____11087 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____11098 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____11098 FStar_Util.set_elements in
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
            let uu____11120 = close_fun env t in desugar_term env uu____11120 in
          let quals1 =
            let uu____11123 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____11123
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____11128 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____11128;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____11136 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____11136 with
           | (t,uu____11144) ->
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
            let uu____11169 =
              let uu____11173 = FStar_Syntax_Syntax.null_binder t in
              [uu____11173] in
            let uu____11174 =
              let uu____11177 =
                let uu____11178 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____11178 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____11177 in
            FStar_Syntax_Util.arrow uu____11169 uu____11174 in
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
            let uu____11222 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11222 with
            | FStar_Pervasives_Native.None  ->
                let uu____11224 =
                  let uu____11225 =
                    let uu____11228 =
                      let uu____11229 =
                        let uu____11230 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11230 " not found" in
                      Prims.strcat "Effect name " uu____11229 in
                    (uu____11228, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11225 in
                raise uu____11224
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11234 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11256 =
                  let uu____11261 =
                    let uu____11265 = desugar_term env t in ([], uu____11265) in
                  FStar_Pervasives_Native.Some uu____11261 in
                (uu____11256, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11283 =
                  let uu____11288 =
                    let uu____11292 = desugar_term env wp in
                    ([], uu____11292) in
                  FStar_Pervasives_Native.Some uu____11288 in
                let uu____11297 =
                  let uu____11302 =
                    let uu____11306 = desugar_term env t in ([], uu____11306) in
                  FStar_Pervasives_Native.Some uu____11302 in
                (uu____11283, uu____11297)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11320 =
                  let uu____11325 =
                    let uu____11329 = desugar_term env t in ([], uu____11329) in
                  FStar_Pervasives_Native.Some uu____11325 in
                (FStar_Pervasives_Native.None, uu____11320) in
          (match uu____11234 with
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
        (fun uu____11389  ->
           fun d  ->
             match uu____11389 with
             | (env1,sigelts) ->
                 let uu____11401 = desugar_decl env1 d in
                 (match uu____11401 with
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
          | (FStar_Pervasives_Native.None ,uu____11446) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11449;
               FStar_Syntax_Syntax.exports = uu____11450;
               FStar_Syntax_Syntax.is_interface = uu____11451;_},FStar_Parser_AST.Module
             (current_lid,uu____11453)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____11458) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11460 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11480 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11480, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11490 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11490, mname, decls, false) in
        match uu____11460 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11508 = desugar_decls env2 decls in
            (match uu____11508 with
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
          let uu____11546 =
            (FStar_Options.interactive ()) &&
              (let uu____11548 =
                 let uu____11549 =
                   let uu____11550 = FStar_Options.file_list () in
                   FStar_List.hd uu____11550 in
                 FStar_Util.get_file_extension uu____11549 in
               uu____11548 = "fsti") in
          if uu____11546 then as_interface m else m in
        let uu____11553 = desugar_modul_common curmod env m1 in
        match uu____11553 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11563 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____11577 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____11577 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11588 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11588
            then
              let uu____11589 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11589
            else ());
           (let uu____11591 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11591, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____11604 =
        FStar_List.fold_left
          (fun uu____11618  ->
             fun m  ->
               match uu____11618 with
               | (env1,mods) ->
                   let uu____11630 = desugar_modul env1 m in
                   (match uu____11630 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11604 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11656 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11656 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11662 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11662
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env