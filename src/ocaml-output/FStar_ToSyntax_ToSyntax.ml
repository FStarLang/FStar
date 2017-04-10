open Prims
let trans_aqual:
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___181_5  ->
    match uu___181_5 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____8 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident Prims.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___182_19  ->
        match uu___182_19 with
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
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | Some effect_id -> FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            Prims.raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline |FStar_Parser_AST.Visible  ->
            Prims.raise (FStar_Errors.Error ("Unsupported qualifier", r))
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___183_25  ->
    match uu___183_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___184_32  ->
    match uu___184_32 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____34 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____67 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____76 -> true
            | uu____79 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____84 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____88 =
      let uu____89 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____89 in
    FStar_Parser_AST.mk_term uu____88 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____93 =
      let uu____94 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____94 in
    FStar_Parser_AST.mk_term uu____93 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let uu____106 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____106 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____110,uu____111) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1
        |FStar_Parser_AST.Ascribed (t1,_,_)|FStar_Parser_AST.LetOpen (_,t1)
          -> is_comp_type env t1
      | uu____117 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____127 =
          let uu____129 =
            let uu____130 =
              let uu____133 = FStar_Parser_AST.compile_op n1 s in
              (uu____133, r) in
            FStar_Ident.mk_ident uu____130 in
          [uu____129] in
        FStar_All.pipe_right uu____127 FStar_Ident.lid_of_ids
let op_as_term:
  FStar_ToSyntax_Env.env ->
    Prims.int ->
      FStar_Range.range ->
        Prims.string -> FStar_Syntax_Syntax.term Prims.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun s  ->
          let r l dd =
            let uu____157 =
              let uu____158 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None in
              FStar_All.pipe_right uu____158 FStar_Syntax_Syntax.fv_to_tm in
            Some uu____157 in
          let fallback uu____163 =
            match s with
            | "=" ->
                r FStar_Syntax_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Syntax_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Syntax_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Syntax_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Syntax_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Syntax_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Syntax_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Syntax_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Syntax_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Syntax_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Syntax_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Syntax_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Syntax_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Syntax_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____165 = FStar_Options.ml_ish () in
                if uu____165
                then
                  r FStar_Syntax_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Syntax_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
            | "^" ->
                r FStar_Syntax_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Syntax_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Syntax_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Syntax_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Syntax_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Syntax_Const.eq2_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "<<" ->
                r FStar_Syntax_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Syntax_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Syntax_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Syntax_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Syntax_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____168 -> None in
          let uu____169 =
            let uu____173 = compile_op_lid arity s rng in
            FStar_ToSyntax_Env.try_lookup_lid env uu____173 in
          match uu____169 with
          | Some t -> Some (Prims.fst t)
          | uu____180 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____190 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____190
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____215 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____218 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____218 with | (env1,uu____225) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____227,term) ->
          let uu____229 = free_type_vars env term in (env, uu____229)
      | FStar_Parser_AST.TAnnotated (id,uu____233) ->
          let uu____234 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____234 with | (env1,uu____241) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____244 = free_type_vars env t in (env, uu____244)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____249 =
        let uu____250 = unparen t in uu____250.FStar_Parser_AST.tm in
      match uu____249 with
      | FStar_Parser_AST.Labeled uu____252 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____258 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____258 with | None  -> [a] | uu____265 -> [])
      | FStar_Parser_AST.Wild 
        |FStar_Parser_AST.Const _
         |FStar_Parser_AST.Uvar _
          |FStar_Parser_AST.Var _
           |FStar_Parser_AST.Projector _
            |FStar_Parser_AST.Discrim _|FStar_Parser_AST.Name _
          -> []
      | FStar_Parser_AST.Assign (_,t1)
        |FStar_Parser_AST.Requires (t1,_)
         |FStar_Parser_AST.Ensures (t1,_)
          |FStar_Parser_AST.NamedTyp (_,t1)|FStar_Parser_AST.Paren t1 ->
          free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____291,ts) ->
          FStar_List.collect
            (fun uu____301  ->
               match uu____301 with | (t1,uu____306) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____307,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____313) ->
          let uu____314 = free_type_vars env t1 in
          let uu____316 = free_type_vars env t2 in
          FStar_List.append uu____314 uu____316
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____320 = free_type_vars_b env b in
          (match uu____320 with
           | (env1,f) ->
               let uu____329 = free_type_vars env1 t1 in
               FStar_List.append f uu____329)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____337 =
            FStar_List.fold_left
              (fun uu____344  ->
                 fun binder  ->
                   match uu____344 with
                   | (env1,free) ->
                       let uu____356 = free_type_vars_b env1 binder in
                       (match uu____356 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____337 with
           | (env1,free) ->
               let uu____374 = free_type_vars env1 body in
               FStar_List.append free uu____374)
      | FStar_Parser_AST.Project (t1,uu____377) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs _
        |FStar_Parser_AST.Let _
         |FStar_Parser_AST.LetOpen _
          |FStar_Parser_AST.If _
           |FStar_Parser_AST.QForall _
            |FStar_Parser_AST.QExists _
             |FStar_Parser_AST.Record _
              |FStar_Parser_AST.Match _
               |FStar_Parser_AST.TryWith _|FStar_Parser_AST.Seq _
          -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____416 =
        let uu____417 = unparen t1 in uu____417.FStar_Parser_AST.tm in
      match uu____416 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____441 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____455 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____455 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____467 =
                     let uu____468 =
                       let uu____471 = tm_type x.FStar_Ident.idRange in
                       (x, uu____471) in
                     FStar_Parser_AST.TAnnotated uu____468 in
                   FStar_Parser_AST.mk_binder uu____467 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
         result)
let close_fun:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____482 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____482 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____494 =
                     let uu____495 =
                       let uu____498 = tm_type x.FStar_Ident.idRange in
                       (x, uu____498) in
                     FStar_Parser_AST.TAnnotated uu____495 in
                   FStar_Parser_AST.mk_binder uu____494 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____500 =
             let uu____501 = unparen t in uu____501.FStar_Parser_AST.tm in
           match uu____500 with
           | FStar_Parser_AST.Product uu____502 -> t
           | uu____506 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Syntax_Const.effect_Tot_lid)
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
      (FStar_Parser_AST.binder Prims.list* FStar_Parser_AST.term)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____527 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____539) -> is_var_pattern p1
    | uu____540 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____545) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____546;
           FStar_Parser_AST.prange = uu____547;_},uu____548)
        -> true
    | uu____554 -> false
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
    | uu____558 -> p
let rec destruct_app_pattern:
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either*
          FStar_Parser_AST.pattern Prims.list* FStar_Parser_AST.term
          Prims.option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____584 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____584 with
             | (name,args,uu____601) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____615);
               FStar_Parser_AST.prange = uu____616;_},args)
            when is_top_level1 ->
            let uu____622 =
              let uu____625 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____625 in
            (uu____622, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____631);
               FStar_Parser_AST.prange = uu____632;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____642 -> failwith "Not an app pattern"
let rec gather_pattern_bound_vars_maybe_top:
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild 
        |FStar_Parser_AST.PatConst _
         |FStar_Parser_AST.PatVar (_,Some (FStar_Parser_AST.Implicit ))
          |FStar_Parser_AST.PatName _
           |FStar_Parser_AST.PatTvar _|FStar_Parser_AST.PatOp _
          -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____677) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____690 = FStar_List.map Prims.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____690
      | FStar_Parser_AST.PatAscribed (pat,uu____695) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____704  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____722 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____742 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___185_760  ->
    match uu___185_760 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____765 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___186_782  ->
        match uu___186_782 with
        | (None ,k) ->
            let uu____791 = FStar_Syntax_Syntax.null_binder k in
            (uu____791, env)
        | (Some a,k) ->
            let uu____795 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____795 with
             | (env1,a1) ->
                 (((let uu___207_806 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___207_806.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___207_806.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____819  ->
    match uu____819 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None
let mk_ref_read tm =
  let tm' =
    let uu____875 =
      let uu____885 =
        let uu____886 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____886 in
      let uu____887 =
        let uu____893 =
          let uu____898 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____898) in
        [uu____893] in
      (uu____885, uu____887) in
    FStar_Syntax_Syntax.Tm_app uu____875 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____932 =
      let uu____942 =
        let uu____943 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____943 in
      let uu____944 =
        let uu____950 =
          let uu____955 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____955) in
        [uu____950] in
      (uu____942, uu____944) in
    FStar_Syntax_Syntax.Tm_app uu____932 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1003 =
      let uu____1013 =
        let uu____1014 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1014 in
      let uu____1015 =
        let uu____1021 =
          let uu____1026 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1026) in
        let uu____1029 =
          let uu____1035 =
            let uu____1040 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1040) in
          [uu____1035] in
        uu____1021 :: uu____1029 in
      (uu____1013, uu____1015) in
    FStar_Syntax_Syntax.Tm_app uu____1003 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___187_1066  ->
    match uu___187_1066 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1067 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1075 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1075)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1086 =
      let uu____1087 = unparen t in uu____1087.FStar_Parser_AST.tm in
    match uu____1086 with
    | FStar_Parser_AST.Wild  ->
        let uu____1090 =
          let uu____1091 = FStar_Unionfind.fresh None in
          FStar_Syntax_Syntax.U_unif uu____1091 in
        FStar_Util.Inr uu____1090
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1097)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < (Prims.parse_int "0")
         then
           Prims.raise
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
         | (FStar_Util.Inl n1,FStar_Util.Inr u)
           |(FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1140 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1140
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1147 =
               let uu____1148 =
                 let uu____1151 =
                   let uu____1152 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1152 in
                 (uu____1151, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1148 in
             Prims.raise uu____1147)
    | FStar_Parser_AST.App uu____1155 ->
        let rec aux t1 univargs =
          let uu____1174 =
            let uu____1175 = unparen t1 in uu____1175.FStar_Parser_AST.tm in
          match uu____1174 with
          | FStar_Parser_AST.App (t2,targ,uu____1180) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___188_1192  ->
                     match uu___188_1192 with
                     | FStar_Util.Inr uu____1195 -> true
                     | uu____1196 -> false) univargs
              then
                let uu____1199 =
                  let uu____1200 =
                    FStar_List.map
                      (fun uu___189_1204  ->
                         match uu___189_1204 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1200 in
                FStar_Util.Inr uu____1199
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___190_1214  ->
                        match uu___190_1214 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1218 -> failwith "impossible")
                     univargs in
                 let uu____1219 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1219)
          | uu____1223 ->
              let uu____1224 =
                let uu____1225 =
                  let uu____1228 =
                    let uu____1229 =
                      let uu____1230 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1230 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1229 in
                  (uu____1228, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1225 in
              Prims.raise uu____1224 in
        aux t []
    | uu____1235 ->
        let uu____1236 =
          let uu____1237 =
            let uu____1240 =
              let uu____1241 =
                let uu____1242 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1242 " in universe context" in
              Prims.strcat "Unexpected term " uu____1241 in
            (uu____1240, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1237 in
        Prims.raise uu____1236
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1276 = FStar_List.hd fields in
  match uu____1276 with
  | (f,uu____1282) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
      let check_field uu____1289 =
        match uu____1289 with
        | (f',uu____1293) ->
            let uu____1294 =
              FStar_ToSyntax_Env.belongs_to_record env f' record in
            if uu____1294
            then ()
            else
              (let msg =
                 FStar_Util.format3
                   "Field %s belongs to record type %s, whereas field %s does not"
                   f.FStar_Ident.str
                   (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                   f'.FStar_Ident.str in
               Prims.raise (FStar_Errors.Error (msg, rg))) in
      ((let uu____1298 = FStar_List.tl fields in
        FStar_List.iter check_field uu____1298);
       (match () with | () -> record))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term _
              |FStar_Syntax_Syntax.Pat_wild _
               |FStar_Syntax_Syntax.Pat_constant _ ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1458,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1480  ->
                          match uu____1480 with
                          | (p3,uu____1486) ->
                              let uu____1487 = pat_vars p3 in
                              FStar_Util.set_union out uu____1487)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1 in
                let uu____1501 =
                  let uu____1502 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3 in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1 in
                  Prims.op_Negation uu____1502 in
                if uu____1501
                then
                  Prims.raise
                    (FStar_Errors.Error
                       ("Disjunctive pattern binds different variables in each case",
                         (p2.FStar_Syntax_Syntax.p)))
                else xs in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1509) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1537 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1537 with
           | Some y -> (l, e, y)
           | uu____1545 ->
               let uu____1547 = push_bv_maybe_mut e x in
               (match uu____1547 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOp op ->
               let uu____1596 =
                 let uu____1597 =
                   let uu____1598 =
                     let uu____1602 =
                       let uu____1603 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op in
                       FStar_Ident.id_of_text uu____1603 in
                     (uu____1602, None) in
                   FStar_Parser_AST.PatVar uu____1598 in
                 {
                   FStar_Parser_AST.pat = uu____1597;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1596
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1615 = aux loc env1 p2 in
               (match uu____1615 with
                | (loc1,env2,var,p3,uu____1634) ->
                    let uu____1639 =
                      FStar_List.fold_left
                        (fun uu____1652  ->
                           fun p4  ->
                             match uu____1652 with
                             | (loc2,env3,ps1) ->
                                 let uu____1675 = aux loc2 env3 p4 in
                                 (match uu____1675 with
                                  | (loc3,env4,uu____1691,p5,uu____1693) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____1639 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1))) in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1737 = aux loc env1 p2 in
               (match uu____1737 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1762 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1768 = close_fun env1 t in
                            desugar_term env1 uu____1768 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1770 -> true)
                           then
                             (let uu____1771 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1772 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1773 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1771 uu____1772 uu____1773)
                           else ();
                           LocalBinder
                             (((let uu___208_1775 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___208_1775.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___208_1775.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1779 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1779, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1789 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1789, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1807 = resolvex loc env1 x in
               (match uu____1807 with
                | (loc1,env2,xbv) ->
                    let uu____1821 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1821, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1832 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1832, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1850;_},args)
               ->
               let uu____1854 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1872  ->
                        match uu____1872 with
                        | (loc1,env2,args1) ->
                            let uu____1902 = aux loc1 env2 arg in
                            (match uu____1902 with
                             | (loc2,env3,uu____1920,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1854 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____1969 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____1969, false))
           | FStar_Parser_AST.PatApp uu____1982 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1995 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2009  ->
                        match uu____2009 with
                        | (loc1,env2,pats1) ->
                            let uu____2031 = aux loc1 env2 pat in
                            (match uu____2031 with
                             | (loc2,env3,uu____2047,pat1,uu____2049) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____1995 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2083 =
                        let uu____2086 =
                          let uu____2091 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2091 in
                        let uu____2092 =
                          let uu____2093 =
                            let uu____2101 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2101, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2093 in
                        FStar_All.pipe_left uu____2086 uu____2092 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2124 =
                               let uu____2125 =
                                 let uu____2133 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2133, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2125 in
                             FStar_All.pipe_left (pos_r r) uu____2124) pats1
                        uu____2083 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2165 =
                 FStar_List.fold_left
                   (fun uu____2182  ->
                      fun p2  ->
                        match uu____2182 with
                        | (loc1,env2,pats) ->
                            let uu____2213 = aux loc1 env2 p2 in
                            (match uu____2213 with
                             | (loc2,env3,uu____2231,pat,uu____2233) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2165 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1 in
                    let l =
                      if dep1
                      then
                        FStar_Syntax_Util.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Syntax_Util.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange in
                    let uu____2304 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2304 with
                     | (constr,uu____2317) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2320 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2322 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2322,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2363  ->
                         match uu____2363 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2378  ->
                         match uu____2378 with
                         | (f,uu____2382) ->
                             let uu____2383 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2395  ->
                                       match uu____2395 with
                                       | (g,uu____2399) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2383 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2402,p2) -> p2))) in
               let app =
                 let uu____2407 =
                   let uu____2408 =
                     let uu____2412 =
                       let uu____2413 =
                         let uu____2414 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2414 in
                       FStar_Parser_AST.mk_pattern uu____2413
                         p1.FStar_Parser_AST.prange in
                     (uu____2412, args) in
                   FStar_Parser_AST.PatApp uu____2408 in
                 FStar_Parser_AST.mk_pattern uu____2407
                   p1.FStar_Parser_AST.prange in
               let uu____2416 = aux loc env1 app in
               (match uu____2416 with
                | (env2,e,b,p2,uu____2435) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2457 =
                            let uu____2458 =
                              let uu____2466 =
                                let uu___209_2467 = fv in
                                let uu____2468 =
                                  let uu____2470 =
                                    let uu____2471 =
                                      let uu____2475 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2475) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2471 in
                                  Some uu____2470 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___209_2467.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___209_2467.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2468
                                } in
                              (uu____2466, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2458 in
                          FStar_All.pipe_left pos uu____2457
                      | uu____2494 -> p2 in
                    (env2, e, b, p3, false)) in
         let uu____2497 = aux [] env p in
         match uu____2497 with
         | (uu____2508,env1,b,p1,uu____2512) ->
             ((let uu____2518 = check_linear_pattern_variables p1 in
               FStar_All.pipe_left Prims.ignore uu____2518);
              (env1, b, p1)))
and desugar_binding_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.option)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2537 =
              let uu____2538 =
                let uu____2541 = FStar_ToSyntax_Env.qualify env x in
                (uu____2541, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2538 in
            (env, uu____2537, None) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2552 =
                  let uu____2553 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x in
                  FStar_Ident.id_of_text uu____2553 in
                mklet uu____2552
            | FStar_Parser_AST.PatVar (x,uu____2555) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2559);
                   FStar_Parser_AST.prange = uu____2560;_},t)
                ->
                let uu____2564 =
                  let uu____2565 =
                    let uu____2568 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2569 = desugar_term env t in
                    (uu____2568, uu____2569) in
                  LetBinder uu____2565 in
                (env, uu____2564, None)
            | uu____2571 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2577 = desugar_data_pat env p is_mut in
             match uu____2577 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2593 -> Some p1 in
                 (env1, binder, p2))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t* bnd* FStar_Syntax_Syntax.pat Prims.option)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat)
  =
  fun uu____2597  ->
    fun env  ->
      fun pat  ->
        let uu____2600 = desugar_data_pat env pat false in
        match uu____2600 with | (env1,uu____2607,pat1) -> (env1, pat1)
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p
and desugar_term:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___210_2614 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___210_2614.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___210_2614.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___210_2614.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___210_2614.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___210_2614.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___210_2614.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___210_2614.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___210_2614.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___210_2614.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___210_2614.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___210_2614.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false;
          FStar_ToSyntax_Env.docs = (uu___210_2614.FStar_ToSyntax_Env.docs)
        } in
      desugar_term_maybe_top false env1 e
and desugar_typ:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___211_2618 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2618.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2618.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2618.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2618.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2618.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2618.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2618.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2618.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2618.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2618.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2618.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true;
          FStar_ToSyntax_Env.docs = (uu___211_2618.FStar_ToSyntax_Env.docs)
        } in
      desugar_term_maybe_top false env1 e
and desugar_machine_integer:
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness* FStar_Const.width) ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2621  ->
        fun range  ->
          match uu____2621 with
          | (signedness,width) ->
              let lid =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (Prims.strcat
                           (match width with
                            | FStar_Const.Int8  -> "8"
                            | FStar_Const.Int16  -> "16"
                            | FStar_Const.Int32  -> "32"
                            | FStar_Const.Int64  -> "64")
                           (Prims.strcat "."
                              (Prims.strcat
                                 (match signedness with
                                  | FStar_Const.Unsigned  -> "u"
                                  | FStar_Const.Signed  -> "") "int_to_t"))))) in
              let lid1 =
                FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range in
              let lid2 =
                let uu____2632 = FStar_ToSyntax_Env.try_lookup_lid env lid1 in
                match uu____2632 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2643 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1) in
                    failwith uu____2643 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range in
              let uu____2660 =
                let uu____2663 =
                  let uu____2664 =
                    let uu____2674 =
                      let uu____2680 =
                        let uu____2685 =
                          FStar_Syntax_Syntax.as_implicit false in
                        (repr1, uu____2685) in
                      [uu____2680] in
                    (lid2, uu____2674) in
                  FStar_Syntax_Syntax.Tm_app uu____2664 in
                FStar_Syntax_Syntax.mk uu____2663 in
              uu____2660 None range
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
            let uu____2720 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2720 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____2738 =
                    let uu____2739 =
                      let uu____2744 = mk_ref_read tm1 in
                      (uu____2744,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2739 in
                  FStar_All.pipe_left mk1 uu____2738
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2758 =
          let uu____2759 = unparen t in uu____2759.FStar_Parser_AST.tm in
        match uu____2758 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2760; FStar_Ident.ident = uu____2761;
              FStar_Ident.nsstr = uu____2762; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2764 ->
            let uu____2765 =
              let uu____2766 =
                let uu____2769 =
                  let uu____2770 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____2770 in
                (uu____2769, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2766 in
            Prims.raise uu____2765 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___212_2798 = e in
          {
            FStar_Syntax_Syntax.n = (uu___212_2798.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___212_2798.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___212_2798.FStar_Syntax_Syntax.vars)
          } in
        let uu____2805 =
          let uu____2806 = unparen top in uu____2806.FStar_Parser_AST.tm in
        match uu____2805 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2807 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int (i,Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op ("=!=",args) ->
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op
                    ("~",
                      [FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Op ("==", args))
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op ("*",uu____2836::uu____2837::[]) when
            let uu____2839 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*" in
            FStar_All.pipe_right uu____2839 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2851 = flatten1 t1 in
                  FStar_List.append uu____2851 [t2]
              | uu____2853 -> [t] in
            let targs =
              let uu____2856 =
                let uu____2858 = unparen top in flatten1 uu____2858 in
              FStar_All.pipe_right uu____2856
                (FStar_List.map
                   (fun t  ->
                      let uu____2862 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____2862)) in
            let uu____2863 =
              let uu____2866 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2866 in
            (match uu____2863 with
             | (tup,uu____2873) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2876 =
              let uu____2879 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              Prims.fst uu____2879 in
            FStar_All.pipe_left setpos uu____2876
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2893 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____2893 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: " s),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____2915 = desugar_term env t in
                             (uu____2915, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2922; FStar_Ident.ident = uu____2923;
              FStar_Ident.nsstr = uu____2924; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2926; FStar_Ident.ident = uu____2927;
              FStar_Ident.nsstr = uu____2928; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2930; FStar_Ident.ident = uu____2931;
               FStar_Ident.nsstr = uu____2932; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2942 =
              let uu____2943 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____2943 in
            mk1 uu____2942
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2944; FStar_Ident.ident = uu____2945;
              FStar_Ident.nsstr = uu____2946; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2948; FStar_Ident.ident = uu____2949;
              FStar_Ident.nsstr = uu____2950; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2952; FStar_Ident.ident = uu____2953;
              FStar_Ident.nsstr = uu____2954; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2958;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2959 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
            (match uu____2959 with
             | Some ed ->
                 let uu____2962 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange in
                 FStar_Syntax_Syntax.fvar uu____2962
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  ->
                 let uu____2963 =
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     (FStar_Ident.text_of_lid eff_name) txt in
                 failwith uu____2963)
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____2967 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____2967 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Can only assign to mutable values",
                           (top.FStar_Parser_AST.range)))
                  else ();
                  mk_ref_assign t1 t21 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l|FStar_Parser_AST.Name l ->
            desugar_name mk1 setpos env true l
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____2983 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____2983 with
              | Some uu____2988 -> Some (true, l)
              | None  ->
                  let uu____2991 =
                    FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                  (match uu____2991 with
                   | Some new_name -> Some (false, new_name)
                   | uu____2999 -> None) in
            (match name with
             | Some (resolve,new_name) ->
                 let uu____3007 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     new_name i in
                 desugar_name mk1 setpos env resolve uu____3007
             | uu____3008 ->
                 let uu____3012 =
                   let uu____3013 =
                     let uu____3016 =
                       FStar_Util.format1
                         "Data constructor or effect %s not found"
                         l.FStar_Ident.str in
                     (uu____3016, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3013 in
                 Prims.raise uu____3012)
        | FStar_Parser_AST.Discrim lid ->
            let uu____3018 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
            (match uu____3018 with
             | None  ->
                 let uu____3020 =
                   let uu____3021 =
                     let uu____3024 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str in
                     (uu____3024, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3021 in
                 Prims.raise uu____3020
             | uu____3025 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 desugar_name mk1 setpos env true lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3036 = FStar_ToSyntax_Env.try_lookup_datacon env l in
            (match uu____3036 with
             | Some head1 ->
                 let uu____3039 =
                   let uu____3044 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                   (uu____3044, true) in
                 (match uu____3039 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3057 ->
                           let uu____3061 =
                             FStar_Util.take
                               (fun uu____3072  ->
                                  match uu____3072 with
                                  | (uu____3075,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args in
                           (match uu____3061 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3108  ->
                                       match uu____3108 with
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
             | None  ->
                 let error_msg =
                   let uu____3140 =
                     FStar_ToSyntax_Env.try_lookup_effect_name env l in
                   match uu____3140 with
                   | None  ->
                       Prims.strcat "Constructor "
                         (Prims.strcat l.FStar_Ident.str " not found")
                   | Some uu____3142 ->
                       Prims.strcat "Effect "
                         (Prims.strcat l.FStar_Ident.str
                            " used at an unexpected position") in
                 Prims.raise
                   (FStar_Errors.Error
                      (error_msg, (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3147 =
              FStar_List.fold_left
                (fun uu____3164  ->
                   fun b  ->
                     match uu____3164 with
                     | (env1,tparams,typs) ->
                         let uu____3195 = desugar_binder env1 b in
                         (match uu____3195 with
                          | (xopt,t1) ->
                              let uu____3211 =
                                match xopt with
                                | None  ->
                                    let uu____3216 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3216)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3211 with
                               | (env2,x) ->
                                   let uu____3228 =
                                     let uu____3230 =
                                       let uu____3232 =
                                         let uu____3233 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3233 in
                                       [uu____3232] in
                                     FStar_List.append typs uu____3230 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___213_3246 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___213_3246.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___213_3246.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3228))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3147 with
             | (env1,uu____3259,targs) ->
                 let uu____3271 =
                   let uu____3274 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3274 in
                 (match uu____3271 with
                  | (tup,uu____3281) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3289 = uncurry binders t in
            (match uu____3289 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___191_3312 =
                   match uu___191_3312 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3322 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3322
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3338 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3338 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3349 = desugar_binder env b in
            (match uu____3349 with
             | (None ,uu____3353) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3359 = as_binder env None b1 in
                 (match uu____3359 with
                  | ((x,uu____3363),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3368 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3368))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3383 =
              FStar_List.fold_left
                (fun uu____3390  ->
                   fun pat  ->
                     match uu____3390 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3405,t) ->
                              let uu____3407 =
                                let uu____3409 = free_type_vars env1 t in
                                FStar_List.append uu____3409 ftvs in
                              (env1, uu____3407)
                          | uu____3412 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3383 with
             | (uu____3415,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3423 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3423 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___192_3452 =
                   match uu___192_3452 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3481 =
                                 let uu____3482 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3482
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3481 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3524 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3524
                   | p::rest ->
                       let uu____3532 = desugar_binding_pat env1 p in
                       (match uu____3532 with
                        | (env2,b,pat) ->
                            let uu____3544 =
                              match b with
                              | LetBinder uu____3563 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3594) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3617 =
                                          let uu____3620 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3620, p1) in
                                        Some uu____3617
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3645,uu____3646) ->
                                             let tup2 =
                                               let uu____3648 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3648
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3652 =
                                                 let uu____3655 =
                                                   let uu____3656 =
                                                     let uu____3666 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____3669 =
                                                       let uu____3671 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____3672 =
                                                         let uu____3674 =
                                                           let uu____3675 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3675 in
                                                         [uu____3674] in
                                                       uu____3671 ::
                                                         uu____3672 in
                                                     (uu____3666, uu____3669) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3656 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3655 in
                                               uu____3652 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____3690 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3690 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3710,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3712,pats)) ->
                                             let tupn =
                                               let uu____3739 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3739
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3749 =
                                                 let uu____3750 =
                                                   let uu____3760 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____3763 =
                                                     let uu____3769 =
                                                       let uu____3775 =
                                                         let uu____3776 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3776 in
                                                       [uu____3775] in
                                                     FStar_List.append args
                                                       uu____3769 in
                                                   (uu____3760, uu____3763) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3750 in
                                               mk1 uu____3749 in
                                             let p2 =
                                               let uu____3791 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3791 in
                                             Some (sc1, p2)
                                         | uu____3815 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3544 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____3856,uu____3857,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3869 =
                let uu____3870 = unparen e in uu____3870.FStar_Parser_AST.tm in
              match uu____3869 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____3876 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____3879 ->
            let rec aux args e =
              let uu____3900 =
                let uu____3901 = unparen e in uu____3901.FStar_Parser_AST.tm in
              match uu____3900 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3911 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3911 in
                  aux (arg :: args) e1
              | uu____3918 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3929 =
              let uu____3930 =
                let uu____3935 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____3935,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____3930 in
            mk1 uu____3929
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____3965 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4007  ->
                        match uu____4007 with
                        | (p,def) ->
                            let uu____4021 = is_app_pattern p in
                            if uu____4021
                            then
                              let uu____4031 =
                                destruct_app_pattern env top_level p in
                              (uu____4031, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4060 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4060, def1)
                               | uu____4075 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4089);
                                           FStar_Parser_AST.prange =
                                             uu____4090;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4103 =
                                            let uu____4111 =
                                              let uu____4114 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4114 in
                                            (uu____4111, [], (Some t)) in
                                          (uu____4103, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4139)
                                        ->
                                        if top_level
                                        then
                                          let uu____4151 =
                                            let uu____4159 =
                                              let uu____4162 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4162 in
                                            (uu____4159, [], None) in
                                          (uu____4151, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4186 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4196 =
                FStar_List.fold_left
                  (fun uu____4220  ->
                     fun uu____4221  ->
                       match (uu____4220, uu____4221) with
                       | ((env1,fnames,rec_bindings),((f,uu____4265,uu____4266),uu____4267))
                           ->
                           let uu____4307 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4321 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4321 with
                                  | (env2,xx) ->
                                      let uu____4332 =
                                        let uu____4334 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4334 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4332))
                             | FStar_Util.Inr l ->
                                 let uu____4339 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4339, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4307 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4196 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4412 =
                    match uu____4412 with
                    | ((uu____4424,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4450 = is_comp_type env1 t in
                                if uu____4450
                                then
                                  ((let uu____4452 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4457 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4457)) in
                                    match uu____4452 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4460 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4461 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4461))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4460
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4466 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4466 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4469 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4479 =
                                let uu____4480 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4480
                                  None in
                              FStar_Util.Inr uu____4479 in
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
                  let uu____4500 =
                    let uu____4501 =
                      let uu____4509 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4509) in
                    FStar_Syntax_Syntax.Tm_let uu____4501 in
                  FStar_All.pipe_left mk1 uu____4500 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4536 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4536 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4557 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4557 None in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Syntax_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t12
                                 }]), body1))
                    | LocalBinder (x,uu____4565) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | None |Some
                            {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild _;
                              FStar_Syntax_Syntax.ty = _;
                              FStar_Syntax_Syntax.p = _;_} -> body1
                          | Some pat3 ->
                              let uu____4574 =
                                let uu____4577 =
                                  let uu____4578 =
                                    let uu____4594 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4595 =
                                      let uu____4597 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1) in
                                      [uu____4597] in
                                    (uu____4594, uu____4595) in
                                  FStar_Syntax_Syntax.Tm_match uu____4578 in
                                FStar_Syntax_Syntax.mk uu____4577 in
                              uu____4574 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4612 =
                          let uu____4613 =
                            let uu____4621 =
                              let uu____4622 =
                                let uu____4623 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4623] in
                              FStar_Syntax_Subst.close uu____4622 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4621) in
                          FStar_Syntax_Syntax.Tm_let uu____4613 in
                        FStar_All.pipe_left mk1 uu____4612 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____4643 = is_rec || (is_app_pattern pat) in
            if uu____4643
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____4649 =
              let uu____4650 =
                let uu____4666 = desugar_term env t1 in
                let uu____4667 =
                  let uu____4677 =
                    let uu____4686 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____4689 = desugar_term env t2 in
                    (uu____4686, None, uu____4689) in
                  let uu____4697 =
                    let uu____4707 =
                      let uu____4716 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____4719 = desugar_term env t3 in
                      (uu____4716, None, uu____4719) in
                    [uu____4707] in
                  uu____4677 :: uu____4697 in
                (uu____4666, uu____4667) in
              FStar_Syntax_Syntax.Tm_match uu____4650 in
            mk1 uu____4649
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   None, e)] r r in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Syntax_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____4805 =
              match uu____4805 with
              | (pat,wopt,b) ->
                  let uu____4815 = desugar_match_pat env pat in
                  (match uu____4815 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4824 = desugar_term env1 e1 in
                             Some uu____4824 in
                       let b1 = desugar_term env1 b in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1)) in
            let uu____4827 =
              let uu____4828 =
                let uu____4844 = desugar_term env e in
                let uu____4845 = FStar_List.map desugar_branch branches in
                (uu____4844, uu____4845) in
              FStar_Syntax_Syntax.Tm_match uu____4828 in
            FStar_All.pipe_left mk1 uu____4827
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____4864 = is_comp_type env t in
              if uu____4864
              then
                let uu____4869 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____4869
              else
                (let uu____4875 = desugar_term env t in
                 FStar_Util.Inl uu____4875) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____4880 =
              let uu____4881 =
                let uu____4899 = desugar_term env e in
                (uu____4899, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____4881 in
            FStar_All.pipe_left mk1 uu____4880
        | FStar_Parser_AST.Record (uu____4915,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____4936 = FStar_List.hd fields in
              match uu____4936 with | (f,uu____4943) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4967  ->
                        match uu____4967 with
                        | (g,uu____4971) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____4975,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4983 =
                         let uu____4984 =
                           let uu____4987 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____4987, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____4984 in
                       Prims.raise uu____4983
                   | Some x ->
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
              | None  ->
                  let uu____4993 =
                    let uu____4999 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5013  ->
                              match uu____5013 with
                              | (f,uu____5019) ->
                                  let uu____5020 =
                                    let uu____5021 = get_field None f in
                                    FStar_All.pipe_left Prims.snd uu____5021 in
                                  (uu____5020, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____4999) in
                  FStar_Parser_AST.Construct uu____4993
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5032 =
                      let uu____5033 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5033 in
                    FStar_Parser_AST.mk_term uu____5032 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5035 =
                      let uu____5042 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5056  ->
                                match uu____5056 with
                                | (f,uu____5062) -> get_field (Some xterm) f)) in
                      (None, uu____5042) in
                    FStar_Parser_AST.Record uu____5035 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
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
                         FStar_Syntax_Syntax.tk = uu____5078;
                         FStar_Syntax_Syntax.pos = uu____5079;
                         FStar_Syntax_Syntax.vars = uu____5080;_},args);
                    FStar_Syntax_Syntax.tk = uu____5082;
                    FStar_Syntax_Syntax.pos = uu____5083;
                    FStar_Syntax_Syntax.vars = uu____5084;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5106 =
                     let uu____5107 =
                       let uu____5117 =
                         let uu____5118 =
                           let uu____5120 =
                             let uu____5121 =
                               let uu____5125 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5125) in
                             FStar_Syntax_Syntax.Record_ctor uu____5121 in
                           Some uu____5120 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5118 in
                       (uu____5117, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5107 in
                   FStar_All.pipe_left mk1 uu____5106 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5149 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5152 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
            (match uu____5152 with
             | (constrname,is_rec) ->
                 let e1 = desugar_term env e in
                 let projname =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     constrname f.FStar_Ident.ident in
                 let qual1 =
                   if is_rec
                   then
                     Some
                       (FStar_Syntax_Syntax.Record_projector
                          (constrname, (f.FStar_Ident.ident)))
                   else None in
                 let uu____5165 =
                   let uu____5166 =
                     let uu____5176 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual1 in
                     let uu____5177 =
                       let uu____5179 = FStar_Syntax_Syntax.as_arg e1 in
                       [uu____5179] in
                     (uu____5176, uu____5177) in
                   FStar_Syntax_Syntax.Tm_app uu____5166 in
                 FStar_All.pipe_left mk1 uu____5165)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5185 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5186 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5187,uu____5188,uu____5189) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5196,uu____5197,uu____5198) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5205,uu____5206,uu____5207) ->
            failwith "Not implemented yet"
and desugar_args:
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term* FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier
        Prims.option) Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5231  ->
              match uu____5231 with
              | (a,imp) ->
                  let uu____5239 = desugar_term env a in
                  arg_withimp_e imp uu____5239))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____5256 =
          match uu____5256 with
          | (t1,uu____5260) ->
              let uu____5261 =
                let uu____5262 = unparen t1 in uu____5262.FStar_Parser_AST.tm in
              (match uu____5261 with
               | FStar_Parser_AST.Requires uu____5263 -> true
               | uu____5267 -> false) in
        let is_ensures uu____5273 =
          match uu____5273 with
          | (t1,uu____5277) ->
              let uu____5278 =
                let uu____5279 = unparen t1 in uu____5279.FStar_Parser_AST.tm in
              (match uu____5278 with
               | FStar_Parser_AST.Ensures uu____5280 -> true
               | uu____5284 -> false) in
        let is_app head1 uu____5293 =
          match uu____5293 with
          | (t1,uu____5297) ->
              let uu____5298 =
                let uu____5299 = unparen t1 in uu____5299.FStar_Parser_AST.tm in
              (match uu____5298 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5301;
                      FStar_Parser_AST.level = uu____5302;_},uu____5303,uu____5304)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5305 -> false) in
        let is_smt_pat uu____5311 =
          match uu____5311 with
          | (t1,uu____5315) ->
              let uu____5316 =
                let uu____5317 = unparen t1 in uu____5317.FStar_Parser_AST.tm in
              (match uu____5316 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5320);
                             FStar_Parser_AST.range = uu____5321;
                             FStar_Parser_AST.level = uu____5322;_},uu____5323)::uu____5324::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5343 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5361 = head_and_args t1 in
          match uu____5361 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing) in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Syntax_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula), None) in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let args1 =
                     match args with
                     | [] ->
                         Prims.raise
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
                   let uu____5578 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5578, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5592 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5592
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5601 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5601
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____5621 ->
                   let default_effect =
                     let uu____5623 = FStar_Options.ml_ish () in
                     if uu____5623
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5626 =
                           FStar_Options.warn_default_effects () in
                         if uu____5626
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Syntax_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____5639 = pre_process_comp_typ t in
        match uu____5639 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5669 =
                  let uu____5670 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5670 in
                fail uu____5669)
             else ();
             (let is_universe uu____5677 =
                match uu____5677 with
                | (uu____5680,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____5682 = FStar_Util.take is_universe args in
              match uu____5682 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5713  ->
                         match uu____5713 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____5718 =
                    let uu____5726 = FStar_List.hd args1 in
                    let uu____5731 = FStar_List.tl args1 in
                    (uu____5726, uu____5731) in
                  (match uu____5718 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____5762 =
                         let is_decrease uu____5785 =
                           match uu____5785 with
                           | (t1,uu____5792) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____5800;
                                       FStar_Syntax_Syntax.pos = uu____5801;
                                       FStar_Syntax_Syntax.vars = uu____5802;_},uu____5803::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____5825 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____5762 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5891  ->
                                      match uu____5891 with
                                      | (t1,uu____5898) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5905,(arg,uu____5907)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5929 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5941 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1) in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Syntax_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Syntax_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Syntax_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Syntax_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Syntax_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Syntax_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else [] in
                                 let flags1 =
                                   FStar_List.append flags cattributes in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Syntax_Const.effect_Lemma_lid
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
                                                 FStar_Syntax_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_succ
                                                      FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 let uu____6033 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6033
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6045 -> pat in
                                         let uu____6046 =
                                           let uu____6053 =
                                             let uu____6060 =
                                               let uu____6066 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6066, aq) in
                                             [uu____6060] in
                                           ens :: uu____6053 in
                                         req :: uu____6046
                                     | uu____6102 -> rest2
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
        | "/\\" -> Some FStar_Syntax_Const.and_lid
        | "\\/" -> Some FStar_Syntax_Const.or_lid
        | "==>" -> Some FStar_Syntax_Const.imp_lid
        | "<==>" -> Some FStar_Syntax_Const.iff_lid
        | "~" -> Some FStar_Syntax_Const.not_lid
        | uu____6118 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let pos t = t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___214_6159 = t in
        {
          FStar_Syntax_Syntax.n = (uu___214_6159.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___214_6159.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___214_6159.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___215_6189 = b in
             {
               FStar_Parser_AST.b = (uu___215_6189.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___215_6189.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___215_6189.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6222 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6222)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6231 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6231 with
             | (env1,a1) ->
                 let a2 =
                   let uu___216_6239 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___216_6239.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___216_6239.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6252 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6261 =
                     let uu____6264 =
                       let uu____6268 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6268] in
                     no_annot_abs uu____6264 body2 in
                   FStar_All.pipe_left setpos uu____6261 in
                 let uu____6273 =
                   let uu____6274 =
                     let uu____6284 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6285 =
                       let uu____6287 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6287] in
                     (uu____6284, uu____6285) in
                   FStar_Syntax_Syntax.Tm_app uu____6274 in
                 FStar_All.pipe_left mk1 uu____6273)
        | uu____6291 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6340 = q (rest, pats, body) in
              let uu____6344 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6340 uu____6344
                FStar_Parser_AST.Formula in
            let uu____6345 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6345 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6350 -> failwith "impossible" in
      let uu____6352 =
        let uu____6353 = unparen f in uu____6353.FStar_Parser_AST.tm in
      match uu____6352 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],_,_)|FStar_Parser_AST.QExists ([],_,_)
          -> failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6383 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6383
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6404 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6404
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6429 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6433 =
        FStar_List.fold_left
          (fun uu____6446  ->
             fun b  ->
               match uu____6446 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___217_6474 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___217_6474.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___217_6474.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___217_6474.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6484 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6484 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___218_6496 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___218_6496.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___218_6496.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6505 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6433 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6555 = desugar_typ env t in ((Some x), uu____6555)
      | FStar_Parser_AST.TVariable x ->
          let uu____6558 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6558)
      | FStar_Parser_AST.NoName t ->
          let uu____6573 = desugar_typ env t in (None, uu____6573)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___193_6622  ->
            match uu___193_6622 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6623 -> false)) in
  let quals2 q =
    let uu____6631 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface in
    if uu____6631
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1 in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d in
          let uu____6638 =
            let uu____6639 =
              let uu____6645 =
                quals2
                  [FStar_Syntax_Syntax.OnlyName;
                  FStar_Syntax_Syntax.Discriminator d] in
              (disc_name, [], FStar_Syntax_Syntax.tun, uu____6645) in
            FStar_Syntax_Syntax.Sig_declare_typ uu____6639 in
          {
            FStar_Syntax_Syntax.sigel = uu____6638;
            FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)
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
            let uu____6670 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6680  ->
                        match uu____6680 with
                        | (x,uu____6685) ->
                            let uu____6686 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____6686 with
                             | (field_name,uu____6691) ->
                                 let only_decl =
                                   ((let uu____6693 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6693)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6694 =
                                        let uu____6695 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____6695.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____6694) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6705 =
                                       FStar_List.filter
                                         (fun uu___194_6707  ->
                                            match uu___194_6707 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6708 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6705
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___195_6716  ->
                                             match uu___195_6716 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6717 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun, quals1));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name)
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6724 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____6724
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____6728 =
                                        let uu____6731 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____6731 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6728;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____6733 =
                                        let uu____6734 =
                                          let uu____6742 =
                                            let uu____6744 =
                                              let uu____6745 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____6745
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____6744] in
                                          ((false, [lb]), uu____6742, quals1,
                                            []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6734 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6733;
                                        FStar_Syntax_Syntax.sigrng = p
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____6670 FStar_List.flatten
let mk_data_projector_names iquals env uu____6785 =
  match uu____6785 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6793,t,uu____6795,n1,quals,uu____6798) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6803 = FStar_Syntax_Util.arrow_formals t in
           (match uu____6803 with
            | (formals,uu____6813) ->
                (match formals with
                 | [] -> []
                 | uu____6827 ->
                     let filter_records uu___196_6835 =
                       match uu___196_6835 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6837,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6844 -> None in
                     let fv_qual =
                       let uu____6846 =
                         FStar_Util.find_map quals filter_records in
                       match uu____6846 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals in
                     let uu____6853 = FStar_Util.first_N n1 formals in
                     (match uu____6853 with
                      | (uu____6865,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6879 -> [])
let mk_typ_abbrev:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
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
                    let uu____6917 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____6917
                    then
                      let uu____6919 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____6919
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____6922 =
                      let uu____6925 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____6925 in
                    let uu____6926 =
                      let uu____6929 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____6929 in
                    let uu____6932 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6922;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6926;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6932
                    } in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let
                         ((false, [lb]), lids, quals, []));
                    FStar_Syntax_Syntax.sigrng = rng
                  }
let rec desugar_tycon:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t* FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___197_6966 =
            match uu___197_6966 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____7005 =
                  let uu____7006 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7006 in
                FStar_Parser_AST.mk_term uu____7005 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,_)|FStar_Parser_AST.TVariable a
                ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Syntax_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | Some (FStar_Parser_AST.Implicit ) -> FStar_Parser_AST.Hash
              | uu____7028 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7031 =
                     let uu____7032 =
                       let uu____7036 = binder_to_term b in
                       (out, uu____7036, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7032 in
                   FStar_Parser_AST.mk_term uu____7031
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___198_7043 =
            match uu___198_7043 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7072  ->
                       match uu____7072 with
                       | (x,t,uu____7079) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7083 =
                    let uu____7084 =
                      let uu____7085 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7085 in
                    FStar_Parser_AST.mk_term uu____7084
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7083 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7088 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7100  ->
                          match uu____7100 with
                          | (x,uu____7106,uu____7107) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7088)
            | uu____7134 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___199_7156 =
            match uu___199_7156 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7170 = typars_of_binders _env binders in
                (match uu____7170 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7198 =
                         let uu____7199 =
                           let uu____7200 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7200 in
                         FStar_Parser_AST.mk_term uu____7199
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7198 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, [], quals1));
                         FStar_Syntax_Syntax.sigrng = rng
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____7211 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7237 =
              FStar_List.fold_left
                (fun uu____7253  ->
                   fun uu____7254  ->
                     match (uu____7253, uu____7254) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7302 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7302 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7237 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7363 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7363
                | uu____7364 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7369 = desugar_abstract_tc quals env [] tc in
              (match uu____7369 with
               | (uu____7376,uu____7377,se,uu____7379) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7382,typars,k,[],[],quals1) ->
                         let quals2 =
                           let uu____7392 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7392
                           then quals1
                           else
                             ((let uu____7397 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7398 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7397 uu____7398);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7402 ->
                               let uu____7403 =
                                 let uu____7406 =
                                   let uu____7407 =
                                     let uu____7415 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7415) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7407 in
                                 FStar_Syntax_Syntax.mk uu____7406 in
                               uu____7403 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___219_7424 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (l, [], t, quals2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___219_7424.FStar_Syntax_Syntax.sigrng)
                         }
                     | uu____7427 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7430 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7430
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7440 = typars_of_binders env binders in
              (match uu____7440 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7460 =
                           FStar_Util.for_some
                             (fun uu___200_7461  ->
                                match uu___200_7461 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7462 -> false) quals in
                         if uu____7460
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7468 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___201_7470  ->
                               match uu___201_7470 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7471 -> false)) in
                     if uu____7468
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7478 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7478
                     then
                       let uu____7480 =
                         let uu____7484 =
                           let uu____7485 = unparen t in
                           uu____7485.FStar_Parser_AST.tm in
                         match uu____7484 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7497 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7513)::args_rev ->
                                   let uu____7520 =
                                     let uu____7521 = unparen last_arg in
                                     uu____7521.FStar_Parser_AST.tm in
                                   (match uu____7520 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7536 -> ([], args))
                               | uu____7541 -> ([], args) in
                             (match uu____7497 with
                              | (cattributes,args1) ->
                                  let uu____7562 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7562))
                         | uu____7568 -> (t, []) in
                       match uu____7480 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let uu____7579 =
                             let uu____7580 =
                               let uu____7589 =
                                 FStar_All.pipe_right quals1
                                   (FStar_List.filter
                                      (fun uu___202_7593  ->
                                         match uu___202_7593 with
                                         | FStar_Syntax_Syntax.Effect  ->
                                             false
                                         | uu____7594 -> true)) in
                               (qlid, [], typars1, c1, uu____7589,
                                 (FStar_List.append cattributes
                                    (FStar_Syntax_Util.comp_flags c1))) in
                             FStar_Syntax_Syntax.Sig_effect_abbrev uu____7580 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____7579;
                             FStar_Syntax_Syntax.sigrng = rng
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7603)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7616 = tycon_record_as_variant trec in
              (match uu____7616 with
               | (t,fs) ->
                   let uu____7626 =
                     let uu____7628 =
                       let uu____7629 =
                         let uu____7634 =
                           let uu____7636 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7636 in
                         (uu____7634, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7629 in
                     uu____7628 :: quals in
                   desugar_tycon env d uu____7626 [t])
          | uu____7639::uu____7640 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____7727 = et in
                match uu____7727 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7841 ->
                         let trec = tc in
                         let uu____7854 = tycon_record_as_variant trec in
                         (match uu____7854 with
                          | (t,fs) ->
                              let uu____7885 =
                                let uu____7887 =
                                  let uu____7888 =
                                    let uu____7893 =
                                      let uu____7895 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____7895 in
                                    (uu____7893, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____7888 in
                                uu____7887 :: quals1 in
                              collect_tcs uu____7885 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7941 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____7941 with
                          | (env2,uu____7972,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8050 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8050 with
                          | (env2,uu____8081,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8145 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8169 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8169 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___204_8419  ->
                             match uu___204_8419 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8455,uu____8456,uu____8457);
                                    FStar_Syntax_Syntax.sigrng = uu____8458;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8491 =
                                     typars_of_binders env1 binders in
                                   match uu____8491 with
                                   | (env2,tpars1) ->
                                       let uu____8508 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8508 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8527 =
                                   let uu____8538 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8538) in
                                 [uu____8527]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8575,tags);
                                    FStar_Syntax_Syntax.sigrng = uu____8577;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____8630 = push_tparams env1 tpars in
                                 (match uu____8630 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8669  ->
                                             match uu____8669 with
                                             | (x,uu____8677) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____8682 =
                                        let uu____8697 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8749  ->
                                                  match uu____8749 with
                                                  | (id,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | Some t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | None  -> tconstr
                                                        else
                                                          (match topt with
                                                           | None  ->
                                                               failwith
                                                                 "Impossible"
                                                           | Some t -> t) in
                                                      let t1 =
                                                        let uu____8782 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____8782 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___203_8788
                                                                 ->
                                                                match uu___203_8788
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8795
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____8801 =
                                                        let uu____8812 =
                                                          let uu____8813 =
                                                            let uu____8814 =
                                                              let uu____8824
                                                                =
                                                                let uu____8827
                                                                  =
                                                                  let uu____8830
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____8830 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____8827 in
                                                              (name, univs,
                                                                uu____8824,
                                                                tname, ntps,
                                                                quals2,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____8814 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____8813;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____8812) in
                                                      (name, uu____8801))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8697 in
                                      (match uu____8682 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames,
                                                      tags));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng
                                             })
                                           :: constrs1))
                             | uu____8955 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9020  ->
                             match uu____9020 with
                             | (name_doc,uu____9035,uu____9036) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9075  ->
                             match uu____9075 with
                             | (uu____9086,uu____9087,se) -> se)) in
                   let uu____9103 =
                     let uu____9107 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9107 rng in
                   (match uu____9103 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9141  ->
                                  match uu____9141 with
                                  | (uu____9153,tps,se) ->
                                      mk_data_projector_names quals env3
                                        (tps, se))) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9185,tps,k,uu____9188,constrs,quals1)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1 in
                                      mk_data_discriminators quals2 env3
                                        tname tps k constrs
                                  | uu____9204 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9213  ->
                                 match uu____9213 with
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
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.binder Prims.list)
  =
  fun env  ->
    fun binders  ->
      let uu____9235 =
        FStar_List.fold_left
          (fun uu____9242  ->
             fun b  ->
               match uu____9242 with
               | (env1,binders1) ->
                   let uu____9254 = desugar_binder env1 b in
                   (match uu____9254 with
                    | (Some a,k) ->
                        let uu____9264 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____9264 with
                         | (env2,a1) ->
                             let uu____9272 =
                               let uu____9274 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___220_9275 = a1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___220_9275.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___220_9275.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    }) in
                               uu____9274 :: binders1 in
                             (env2, uu____9272))
                    | uu____9277 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9235 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let rec desugar_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                  Prims.list)
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
                let uu____9355 = desugar_binders monad_env eff_binders in
                match uu____9355 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9368 =
                        let uu____9369 =
                          let uu____9373 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          Prims.fst uu____9373 in
                        FStar_List.length uu____9369 in
                      uu____9368 = (Prims.parse_int "1") in
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
                          (uu____9401,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9403,uu____9404,uu____9405),uu____9406)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9423 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9424 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9430 = name_of_eff_decl decl in
                           FStar_List.mem uu____9430 mandatory_members)
                        eff_decls in
                    (match uu____9424 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9440 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9451  ->
                                   fun decl  ->
                                     match uu____9451 with
                                     | (env2,out) ->
                                         let uu____9463 =
                                           desugar_decl env2 decl in
                                         (match uu____9463 with
                                          | (env3,ses) ->
                                              let uu____9471 =
                                                let uu____9473 =
                                                  FStar_List.hd ses in
                                                uu____9473 :: out in
                                              (env3, uu____9471))) (env1, [])) in
                         (match uu____9440 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9501,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9503,uu____9504,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9505,
                                                               (def,uu____9507)::
                                                               (cps_type,uu____9509)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9510;
                                                            FStar_Parser_AST.level
                                                              = uu____9511;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9538 =
                                              let uu____9539 =
                                                FStar_ToSyntax_Env.qualify
                                                  env2 name in
                                              let uu____9540 =
                                                let uu____9541 =
                                                  desugar_term env2 def in
                                                FStar_Syntax_Subst.close
                                                  binders1 uu____9541 in
                                              let uu____9542 =
                                                let uu____9543 =
                                                  desugar_typ env2 cps_type in
                                                FStar_Syntax_Subst.close
                                                  binders1 uu____9543 in
                                              {
                                                FStar_Syntax_Syntax.action_name
                                                  = uu____9539;
                                                FStar_Syntax_Syntax.action_unqualified_name
                                                  = name;
                                                FStar_Syntax_Syntax.action_univs
                                                  = [];
                                                FStar_Syntax_Syntax.action_defn
                                                  = uu____9540;
                                                FStar_Syntax_Syntax.action_typ
                                                  = uu____9542
                                              } in
                                            (uu____9538, doc1)
                                        | FStar_Parser_AST.Tycon
                                            (uu____9545,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9547,uu____9548,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9567 =
                                              let uu____9568 =
                                                FStar_ToSyntax_Env.qualify
                                                  env2 name in
                                              let uu____9569 =
                                                let uu____9570 =
                                                  desugar_term env2 defn in
                                                FStar_Syntax_Subst.close
                                                  binders1 uu____9570 in
                                              {
                                                FStar_Syntax_Syntax.action_name
                                                  = uu____9568;
                                                FStar_Syntax_Syntax.action_unqualified_name
                                                  = name;
                                                FStar_Syntax_Syntax.action_univs
                                                  = [];
                                                FStar_Syntax_Syntax.action_defn
                                                  = uu____9569;
                                                FStar_Syntax_Syntax.action_typ
                                                  = FStar_Syntax_Syntax.tun
                                              } in
                                            (uu____9567, doc1)
                                        | uu____9572 ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let actions1 =
                                FStar_List.map Prims.fst actions_docs in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____9591 =
                                  let uu____9592 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9592 in
                                ([], uu____9591) in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (Some mname)) quals in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____9604 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____9604) in
                                  let uu____9614 =
                                    let uu____9615 =
                                      let uu____9616 =
                                        let uu____9617 = lookup "repr" in
                                        Prims.snd uu____9617 in
                                      let uu____9622 = lookup "return" in
                                      let uu____9623 = lookup "bind" in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          qualifiers;
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
                                        FStar_Syntax_Syntax.repr = uu____9616;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9622;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9623;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9615 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9614;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange)
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___205_9626  ->
                                          match uu___205_9626 with
                                          | FStar_Syntax_Syntax.Reifiable 
                                            |FStar_Syntax_Syntax.Reflectable
                                            _ -> true
                                          | uu____9628 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9634 =
                                     let uu____9635 =
                                       let uu____9636 = lookup "return_wp" in
                                       let uu____9637 = lookup "bind_wp" in
                                       let uu____9638 = lookup "if_then_else" in
                                       let uu____9639 = lookup "ite_wp" in
                                       let uu____9640 = lookup "stronger" in
                                       let uu____9641 = lookup "close_wp" in
                                       let uu____9642 = lookup "assert_p" in
                                       let uu____9643 = lookup "assume_p" in
                                       let uu____9644 = lookup "null_wp" in
                                       let uu____9645 = lookup "trivial" in
                                       let uu____9646 =
                                         if rr
                                         then
                                           let uu____9647 = lookup "repr" in
                                           FStar_All.pipe_left Prims.snd
                                             uu____9647
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____9656 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____9658 =
                                         if rr then lookup "bind" else un_ts in
                                       {
                                         FStar_Syntax_Syntax.qualifiers =
                                           qualifiers;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____9636;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9637;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9638;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9639;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9640;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9641;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9642;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9643;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9644;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9645;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9646;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9656;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9658;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9635 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9634;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange)
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
                                        fun uu____9671  ->
                                          match uu____9671 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____9680 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____9680 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____9682 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____9682
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env) in
                                  let refl_decl =
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_declare_typ
                                           (reflect_lid, [],
                                             FStar_Syntax_Syntax.tun,
                                             [FStar_Syntax_Syntax.Assumption;
                                             FStar_Syntax_Syntax.Reflectable
                                               mname]));
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange)
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
      (FStar_Ident.lident Prims.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                  Prims.list)
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
                let uu____9706 = desugar_binders env1 eff_binders in
                match uu____9706 with
                | (env2,binders) ->
                    let uu____9717 =
                      let uu____9727 = head_and_args defn in
                      match uu____9727 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____9752 ->
                                let uu____9753 =
                                  let uu____9754 =
                                    let uu____9757 =
                                      let uu____9758 =
                                        let uu____9759 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____9759 " not found" in
                                      Prims.strcat "Effect " uu____9758 in
                                    (uu____9757, (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____9754 in
                                Prims.raise uu____9753 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____9761 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9777)::args_rev ->
                                let uu____9784 =
                                  let uu____9785 = unparen last_arg in
                                  uu____9785.FStar_Parser_AST.tm in
                                (match uu____9784 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____9800 -> ([], args))
                            | uu____9805 -> ([], args) in
                          (match uu____9761 with
                           | (cattributes,args1) ->
                               let uu____9832 = desugar_args env2 args1 in
                               let uu____9837 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____9832, uu____9837)) in
                    (match uu____9717 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____9871 =
                           match uu____9871 with
                           | (uu____9878,x) ->
                               let uu____9882 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____9882 with
                                | (edb,x1) ->
                                    (if
                                       (FStar_List.length args) <>
                                         (FStar_List.length edb)
                                     then
                                       Prims.raise
                                         (FStar_Errors.Error
                                            ("Unexpected number of arguments to effect constructor",
                                              (defn.FStar_Parser_AST.range)))
                                     else ();
                                     (let s =
                                        FStar_Syntax_Util.subst_of_list edb
                                          args in
                                      let uu____9902 =
                                        let uu____9903 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____9903 in
                                      ([], uu____9902)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____9907 =
                             let uu____9909 = trans_qual1 (Some mname) in
                             FStar_List.map uu____9909 quals in
                           let uu____9912 =
                             let uu____9913 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             Prims.snd uu____9913 in
                           let uu____9919 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____9920 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____9921 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____9922 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____9923 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____9924 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____9925 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____9926 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____9927 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____9928 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____9929 =
                             let uu____9930 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             Prims.snd uu____9930 in
                           let uu____9936 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____9937 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____9938 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____9941 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____9942 =
                                    let uu____9943 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    Prims.snd uu____9943 in
                                  let uu____9949 =
                                    let uu____9950 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    Prims.snd uu____9950 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____9941;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____9942;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____9949
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.qualifiers = uu____9907;
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____9912;
                             FStar_Syntax_Syntax.ret_wp = uu____9919;
                             FStar_Syntax_Syntax.bind_wp = uu____9920;
                             FStar_Syntax_Syntax.if_then_else = uu____9921;
                             FStar_Syntax_Syntax.ite_wp = uu____9922;
                             FStar_Syntax_Syntax.stronger = uu____9923;
                             FStar_Syntax_Syntax.close_wp = uu____9924;
                             FStar_Syntax_Syntax.assert_p = uu____9925;
                             FStar_Syntax_Syntax.assume_p = uu____9926;
                             FStar_Syntax_Syntax.null_wp = uu____9927;
                             FStar_Syntax_Syntax.trivial = uu____9928;
                             FStar_Syntax_Syntax.repr = uu____9929;
                             FStar_Syntax_Syntax.return_repr = uu____9936;
                             FStar_Syntax_Syntax.bind_repr = uu____9937;
                             FStar_Syntax_Syntax.actions = uu____9938
                           } in
                         let se =
                           let for_free =
                             let uu____9958 =
                               let uu____9959 =
                                 let uu____9963 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 Prims.fst uu____9963 in
                               FStar_List.length uu____9959 in
                             uu____9958 = (Prims.parse_int "1") in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange)
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
                                       let uu____9992 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____9992 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____9994 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____9994
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env) in
                             let refl_decl =
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (reflect_lid, [],
                                        FStar_Syntax_Syntax.tun,
                                        [FStar_Syntax_Syntax.Assumption;
                                        FStar_Syntax_Syntax.Reflectable mname]));
                                 FStar_Syntax_Syntax.sigrng =
                                   (d.FStar_Parser_AST.drange)
                               } in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5 in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc in
                         (env7, [se]))
and desugar_decl:
  env_t -> FStar_Parser_AST.decl -> (env_t* FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____10020 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10032 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10032, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10053  ->
                 match uu____10053 with | (x,uu____10058) -> x) tcs in
          let uu____10061 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10061 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp _;
                    FStar_Parser_AST.prange = _;_},_)::[]
                 |({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar _;
                     FStar_Parser_AST.prange = _;_},_)::[]
                  |({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar _;
                           FStar_Parser_AST.prange = _;_},_);
                      FStar_Parser_AST.prange = _;_},_)::[]
                   -> false
               | (p,uu____10100)::[] ->
                   let uu____10105 = is_app_pattern p in
                   Prims.op_Negation uu____10105
               | uu____10106 -> false) in
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
            let uu____10117 =
              let uu____10118 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10118.FStar_Syntax_Syntax.n in
            (match uu____10117 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10124) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10144::uu____10145 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10147 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___206_10151  ->
                               match uu___206_10151 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10153;
                                   FStar_Syntax_Syntax.lbunivs = uu____10154;
                                   FStar_Syntax_Syntax.lbtyp = uu____10155;
                                   FStar_Syntax_Syntax.lbeff = uu____10156;
                                   FStar_Syntax_Syntax.lbdef = uu____10157;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10164;
                                   FStar_Syntax_Syntax.lbtyp = uu____10165;
                                   FStar_Syntax_Syntax.lbeff = uu____10166;
                                   FStar_Syntax_Syntax.lbdef = uu____10167;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10179 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10185  ->
                             match uu____10185 with
                             | (uu____10188,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10179
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10196 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10196
                   then
                     let uu____10201 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___221_10208 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___222_10209 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___222_10209.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___222_10209.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___221_10208.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___221_10208.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___221_10208.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___221_10208.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((Prims.fst lbs), uu____10201)
                   else lbs in
                 let names =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let
                          (lbs1, names, quals2, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                   } in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names in
                 (env2, [s])
             | uu____10237 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10241 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10252 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10241 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar (fresh_toplevel_name, None))
                       FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___223_10268 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___223_10268.FStar_Parser_AST.prange)
                       }
                   | uu____10269 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___224_10273 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___224_10273.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___224_10273.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___224_10273.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10292 id =
                   match uu____10292 with
                   | (env1,ses) ->
                       let main =
                         let uu____10305 =
                           let uu____10306 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10306 in
                         FStar_Parser_AST.mk_term uu____10305
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id] in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main, [(pat, None, projectee)]))
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (id, None))
                           FStar_Range.dummyRange in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____10334 = desugar_decl env1 id_decl in
                       (match uu____10334 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10345 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10345 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
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
                 (FStar_Syntax_Syntax.Sig_assume
                    (lid, f, [FStar_Syntax_Syntax.Assumption]));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____10367 = close_fun env t in desugar_term env uu____10367 in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10374 =
              let uu____10375 =
                let uu____10381 = FStar_List.map (trans_qual1 None) quals1 in
                (lid, [], t1, uu____10381) in
              FStar_Syntax_Syntax.Sig_declare_typ uu____10375 in
            {
              FStar_Syntax_Syntax.sigel = uu____10374;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10390 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10390 with
           | (t,uu____10398) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Syntax_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Syntax_Syntax.ExceptionConstructor],
                          [FStar_Syntax_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle
                        ([se], [FStar_Syntax_Syntax.ExceptionConstructor],
                          [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 } in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
               let data_ops = mk_data_projector_names [] env2 ([], se) in
               let discs =
                 mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l] in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____10426 =
              let uu____10430 = FStar_Syntax_Syntax.null_binder t in
              [uu____10430] in
            let uu____10431 =
              let uu____10434 =
                let uu____10435 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                Prims.fst uu____10435 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10434 in
            FStar_Syntax_Util.arrow uu____10426 uu____10431 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
          let data_ops = mk_data_projector_names [] env2 ([], se) in
          let discs =
            mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l] in
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
            let uu____10482 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10482 with
            | None  ->
                let uu____10484 =
                  let uu____10485 =
                    let uu____10488 =
                      let uu____10489 =
                        let uu____10490 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10490 " not found" in
                      Prims.strcat "Effect name " uu____10489 in
                    (uu____10488, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10485 in
                Prims.raise uu____10484
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10494 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10516 =
                  let uu____10521 =
                    let uu____10525 = desugar_term env t in ([], uu____10525) in
                  Some uu____10521 in
                (uu____10516, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10543 =
                  let uu____10548 =
                    let uu____10552 = desugar_term env wp in
                    ([], uu____10552) in
                  Some uu____10548 in
                let uu____10557 =
                  let uu____10562 =
                    let uu____10566 = desugar_term env t in ([], uu____10566) in
                  Some uu____10562 in
                (uu____10543, uu____10557)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10580 =
                  let uu____10585 =
                    let uu____10589 = desugar_term env t in ([], uu____10589) in
                  Some uu____10585 in
                (None, uu____10580) in
          (match uu____10494 with
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
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 } in
               (env, [se]))
let desugar_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10640  ->
           fun d  ->
             match uu____10640 with
             | (env1,sigelts) ->
                 let uu____10652 = desugar_decl env1 d in
                 (match uu____10652 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
let open_prims_all:
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Syntax_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Syntax_Const.all_lid)
    FStar_Range.dummyRange]
let desugar_modul_common:
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t* FStar_Syntax_Syntax.modul* Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (None ,uu____10694) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10697;
               FStar_Syntax_Syntax.exports = uu____10698;
               FStar_Syntax_Syntax.is_interface = uu____10699;_},FStar_Parser_AST.Module
             (current_lid,uu____10701)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10706) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____10708 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10728 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____10728, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10738 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____10738, mname, decls, false) in
        match uu____10708 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10756 = desugar_decls env2 decls in
            (match uu____10756 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   } in
                 (env3, modul, pop_when_done))
let desugar_partial_modul:
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____10781 =
            (FStar_Options.interactive ()) &&
              (let uu____10782 =
                 let uu____10783 =
                   let uu____10784 = FStar_Options.file_list () in
                   FStar_List.hd uu____10784 in
                 FStar_Util.get_file_extension uu____10783 in
               uu____10782 = "fsti") in
          if uu____10781
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10792,uu____10793) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m in
        let uu____10797 = desugar_modul_common curmod env m1 in
        match uu____10797 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10807 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10819 = desugar_modul_common None env m in
      match uu____10819 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____10830 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____10830
            then
              let uu____10831 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____10831
            else ());
           (let uu____10833 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____10833, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10844 =
        FStar_List.fold_left
          (fun uu____10851  ->
             fun m  ->
               match uu____10851 with
               | (env1,mods) ->
                   let uu____10863 = desugar_modul env1 m in
                   (match uu____10863 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____10844 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10887 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____10887 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___225_10893 = en1 in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___225_10893.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___225_10893.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___225_10893.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___225_10893.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___225_10893.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___225_10893.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___225_10893.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___225_10893.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___225_10893.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___225_10893.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___225_10893.FStar_ToSyntax_Env.expect_typ);
                 FStar_ToSyntax_Env.docs =
                   (uu___225_10893.FStar_ToSyntax_Env.docs)
               }) m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env