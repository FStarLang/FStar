open Prims
let sigelt_of_decl:
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.sigelt' -> FStar_Syntax_Syntax.sigelt
  =
  fun d  ->
    fun e  ->
      {
        FStar_Syntax_Syntax.sigel = e;
        FStar_Syntax_Syntax.sigdoc = (d.FStar_Parser_AST.doc);
        FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
      }
let trans_aqual:
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___181_11  ->
    match uu___181_11 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____14 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident Prims.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___182_25  ->
        match uu___182_25 with
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
  fun uu___183_31  ->
    match uu___183_31 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___184_38  ->
    match uu___184_38 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____40 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____73 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____82 -> true
            | uu____85 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____90 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____94 =
      let uu____95 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____95 in
    FStar_Parser_AST.mk_term uu____94 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____99 =
      let uu____100 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____100 in
    FStar_Parser_AST.mk_term uu____99 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let uu____112 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____112 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____116,uu____117) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1
        |FStar_Parser_AST.Ascribed (t1,_,_)|FStar_Parser_AST.LetOpen (_,t1)
          -> is_comp_type env t1
      | uu____123 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____133 =
          let uu____135 =
            let uu____136 =
              let uu____139 = FStar_Parser_AST.compile_op n1 s in
              (uu____139, r) in
            FStar_Ident.mk_ident uu____136 in
          [uu____135] in
        FStar_All.pipe_right uu____133 FStar_Ident.lid_of_ids
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
            let uu____163 =
              let uu____164 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None in
              FStar_All.pipe_right uu____164 FStar_Syntax_Syntax.fv_to_tm in
            Some uu____163 in
          let fallback uu____169 =
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
                let uu____171 = FStar_Options.ml_ish () in
                if uu____171
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
            | uu____174 -> None in
          let uu____175 =
            let uu____179 = compile_op_lid arity s rng in
            FStar_ToSyntax_Env.try_lookup_lid env uu____179 in
          match uu____175 with
          | Some t -> Some (Prims.fst t)
          | uu____186 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____196 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____196
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____221 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____224 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____224 with | (env1,uu____231) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____233,term) ->
          let uu____235 = free_type_vars env term in (env, uu____235)
      | FStar_Parser_AST.TAnnotated (id,uu____239) ->
          let uu____240 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____240 with | (env1,uu____247) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____250 = free_type_vars env t in (env, uu____250)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____255 =
        let uu____256 = unparen t in uu____256.FStar_Parser_AST.tm in
      match uu____255 with
      | FStar_Parser_AST.Labeled uu____258 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____264 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____264 with | None  -> [a] | uu____271 -> [])
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
      | FStar_Parser_AST.Construct (uu____297,ts) ->
          FStar_List.collect
            (fun uu____307  ->
               match uu____307 with | (t1,uu____312) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____313,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____319) ->
          let uu____320 = free_type_vars env t1 in
          let uu____322 = free_type_vars env t2 in
          FStar_List.append uu____320 uu____322
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____326 = free_type_vars_b env b in
          (match uu____326 with
           | (env1,f) ->
               let uu____335 = free_type_vars env1 t1 in
               FStar_List.append f uu____335)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____343 =
            FStar_List.fold_left
              (fun uu____350  ->
                 fun binder  ->
                   match uu____350 with
                   | (env1,free) ->
                       let uu____362 = free_type_vars_b env1 binder in
                       (match uu____362 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____343 with
           | (env1,free) ->
               let uu____380 = free_type_vars env1 body in
               FStar_List.append free uu____380)
      | FStar_Parser_AST.Project (t1,uu____383) -> free_type_vars env t1
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
      let uu____422 =
        let uu____423 = unparen t1 in uu____423.FStar_Parser_AST.tm in
      match uu____422 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____447 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____461 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____461 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____473 =
                     let uu____474 =
                       let uu____477 = tm_type x.FStar_Ident.idRange in
                       (x, uu____477) in
                     FStar_Parser_AST.TAnnotated uu____474 in
                   FStar_Parser_AST.mk_binder uu____473 x.FStar_Ident.idRange
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
        let uu____488 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____488 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____500 =
                     let uu____501 =
                       let uu____504 = tm_type x.FStar_Ident.idRange in
                       (x, uu____504) in
                     FStar_Parser_AST.TAnnotated uu____501 in
                   FStar_Parser_AST.mk_binder uu____500 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____506 =
             let uu____507 = unparen t in uu____507.FStar_Parser_AST.tm in
           match uu____506 with
           | FStar_Parser_AST.Product uu____508 -> t
           | uu____512 ->
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
      | uu____533 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____545) -> is_var_pattern p1
    | uu____546 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____551) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____552;
           FStar_Parser_AST.prange = uu____553;_},uu____554)
        -> true
    | uu____560 -> false
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
    | uu____564 -> p
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
            let uu____590 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____590 with
             | (name,args,uu____607) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____621);
               FStar_Parser_AST.prange = uu____622;_},args)
            when is_top_level1 ->
            let uu____628 =
              let uu____631 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____631 in
            (uu____628, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____637);
               FStar_Parser_AST.prange = uu____638;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____648 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatVar (x,uu____683) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____696 = FStar_List.map Prims.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____696
      | FStar_Parser_AST.PatAscribed (pat,uu____701) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____710  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____728 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____748 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___185_766  ->
    match uu___185_766 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____771 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___186_788  ->
        match uu___186_788 with
        | (None ,k) ->
            let uu____797 = FStar_Syntax_Syntax.null_binder k in
            (uu____797, env)
        | (Some a,k) ->
            let uu____801 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____801 with
             | (env1,a1) ->
                 (((let uu___207_812 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___207_812.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___207_812.FStar_Syntax_Syntax.index);
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
  fun uu____825  ->
    match uu____825 with
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
    let uu____881 =
      let uu____891 =
        let uu____892 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____892 in
      let uu____893 =
        let uu____899 =
          let uu____904 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____904) in
        [uu____899] in
      (uu____891, uu____893) in
    FStar_Syntax_Syntax.Tm_app uu____881 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____938 =
      let uu____948 =
        let uu____949 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____949 in
      let uu____950 =
        let uu____956 =
          let uu____961 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____961) in
        [uu____956] in
      (uu____948, uu____950) in
    FStar_Syntax_Syntax.Tm_app uu____938 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1009 =
      let uu____1019 =
        let uu____1020 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1020 in
      let uu____1021 =
        let uu____1027 =
          let uu____1032 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1032) in
        let uu____1035 =
          let uu____1041 =
            let uu____1046 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1046) in
          [uu____1041] in
        uu____1027 :: uu____1035 in
      (uu____1019, uu____1021) in
    FStar_Syntax_Syntax.Tm_app uu____1009 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___187_1072  ->
    match uu___187_1072 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1073 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1081 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1081)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1092 =
      let uu____1093 = unparen t in uu____1093.FStar_Parser_AST.tm in
    match uu____1092 with
    | FStar_Parser_AST.Wild  ->
        let uu____1096 =
          let uu____1097 = FStar_Unionfind.fresh None in
          FStar_Syntax_Syntax.U_unif uu____1097 in
        FStar_Util.Inr uu____1096
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1103)) ->
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
             let uu____1146 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1146
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1153 =
               let uu____1154 =
                 let uu____1157 =
                   let uu____1158 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1158 in
                 (uu____1157, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1154 in
             Prims.raise uu____1153)
    | FStar_Parser_AST.App uu____1161 ->
        let rec aux t1 univargs =
          let uu____1180 =
            let uu____1181 = unparen t1 in uu____1181.FStar_Parser_AST.tm in
          match uu____1180 with
          | FStar_Parser_AST.App (t2,targ,uu____1186) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___188_1198  ->
                     match uu___188_1198 with
                     | FStar_Util.Inr uu____1201 -> true
                     | uu____1202 -> false) univargs
              then
                let uu____1205 =
                  let uu____1206 =
                    FStar_List.map
                      (fun uu___189_1210  ->
                         match uu___189_1210 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1206 in
                FStar_Util.Inr uu____1205
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___190_1220  ->
                        match uu___190_1220 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1224 -> failwith "impossible")
                     univargs in
                 let uu____1225 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1225)
          | uu____1229 ->
              let uu____1230 =
                let uu____1231 =
                  let uu____1234 =
                    let uu____1235 =
                      let uu____1236 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1236 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1235 in
                  (uu____1234, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1231 in
              Prims.raise uu____1230 in
        aux t []
    | uu____1241 ->
        let uu____1242 =
          let uu____1243 =
            let uu____1246 =
              let uu____1247 =
                let uu____1248 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1248 " in universe context" in
              Prims.strcat "Unexpected term " uu____1247 in
            (uu____1246, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1243 in
        Prims.raise uu____1242
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1282 = FStar_List.hd fields in
  match uu____1282 with
  | (f,uu____1288) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
      let check_field uu____1295 =
        match uu____1295 with
        | (f',uu____1299) ->
            let uu____1300 =
              FStar_ToSyntax_Env.belongs_to_record env f' record in
            if uu____1300
            then ()
            else
              (let msg =
                 FStar_Util.format3
                   "Field %s belongs to record type %s, whereas field %s does not"
                   f.FStar_Ident.str
                   (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                   f'.FStar_Ident.str in
               Prims.raise (FStar_Errors.Error (msg, rg))) in
      ((let uu____1304 = FStar_List.tl fields in
        FStar_List.iter check_field uu____1304);
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1464,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1486  ->
                          match uu____1486 with
                          | (p3,uu____1492) ->
                              let uu____1493 = pat_vars p3 in
                              FStar_Util.set_union out uu____1493)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1 in
                let uu____1507 =
                  let uu____1508 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3 in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1 in
                  Prims.op_Negation uu____1508 in
                if uu____1507
                then
                  Prims.raise
                    (FStar_Errors.Error
                       ("Disjunctive pattern binds different variables in each case",
                         (p2.FStar_Syntax_Syntax.p)))
                else xs in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1515) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1543 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1543 with
           | Some y -> (l, e, y)
           | uu____1551 ->
               let uu____1553 = push_bv_maybe_mut e x in
               (match uu____1553 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
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
               let uu____1602 =
                 let uu____1603 =
                   let uu____1604 =
                     let uu____1608 =
                       let uu____1609 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op in
                       FStar_Ident.id_of_text uu____1609 in
                     (uu____1608, None) in
                   FStar_Parser_AST.PatVar uu____1604 in
                 {
                   FStar_Parser_AST.pat = uu____1603;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1602
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1621 = aux loc env1 p2 in
               (match uu____1621 with
                | (loc1,env2,var,p3,uu____1640) ->
                    let uu____1645 =
                      FStar_List.fold_left
                        (fun uu____1658  ->
                           fun p4  ->
                             match uu____1658 with
                             | (loc2,env3,ps1) ->
                                 let uu____1681 = aux loc2 env3 p4 in
                                 (match uu____1681 with
                                  | (loc3,env4,uu____1697,p5,uu____1699) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____1645 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1))) in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1743 = aux loc env1 p2 in
               (match uu____1743 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1768 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1774 = close_fun env1 t in
                            desugar_term env1 uu____1774 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1776 -> true)
                           then
                             (let uu____1777 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1778 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1779 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1777 uu____1778 uu____1779)
                           else ();
                           LocalBinder
                             (((let uu___208_1781 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___208_1781.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___208_1781.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1785 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1785, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1795 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1795, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1813 = resolvex loc env1 x in
               (match uu____1813 with
                | (loc1,env2,xbv) ->
                    let uu____1827 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1827, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1838 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1838, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1856;_},args)
               ->
               let uu____1860 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1878  ->
                        match uu____1878 with
                        | (loc1,env2,args1) ->
                            let uu____1908 = aux loc1 env2 arg in
                            (match uu____1908 with
                             | (loc2,env3,uu____1926,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1860 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____1975 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____1975, false))
           | FStar_Parser_AST.PatApp uu____1988 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2001 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2015  ->
                        match uu____2015 with
                        | (loc1,env2,pats1) ->
                            let uu____2037 = aux loc1 env2 pat in
                            (match uu____2037 with
                             | (loc2,env3,uu____2053,pat1,uu____2055) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2001 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2089 =
                        let uu____2092 =
                          let uu____2097 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2097 in
                        let uu____2098 =
                          let uu____2099 =
                            let uu____2107 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2107, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2099 in
                        FStar_All.pipe_left uu____2092 uu____2098 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2130 =
                               let uu____2131 =
                                 let uu____2139 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2139, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2131 in
                             FStar_All.pipe_left (pos_r r) uu____2130) pats1
                        uu____2089 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2171 =
                 FStar_List.fold_left
                   (fun uu____2188  ->
                      fun p2  ->
                        match uu____2188 with
                        | (loc1,env2,pats) ->
                            let uu____2219 = aux loc1 env2 p2 in
                            (match uu____2219 with
                             | (loc2,env3,uu____2237,pat,uu____2239) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2171 with
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
                    let uu____2310 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2310 with
                     | (constr,uu____2323) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2326 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2328 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2328,
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
                      (fun uu____2369  ->
                         match uu____2369 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2384  ->
                         match uu____2384 with
                         | (f,uu____2388) ->
                             let uu____2389 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2401  ->
                                       match uu____2401 with
                                       | (g,uu____2405) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2389 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2408,p2) -> p2))) in
               let app =
                 let uu____2413 =
                   let uu____2414 =
                     let uu____2418 =
                       let uu____2419 =
                         let uu____2420 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2420 in
                       FStar_Parser_AST.mk_pattern uu____2419
                         p1.FStar_Parser_AST.prange in
                     (uu____2418, args) in
                   FStar_Parser_AST.PatApp uu____2414 in
                 FStar_Parser_AST.mk_pattern uu____2413
                   p1.FStar_Parser_AST.prange in
               let uu____2422 = aux loc env1 app in
               (match uu____2422 with
                | (env2,e,b,p2,uu____2441) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2463 =
                            let uu____2464 =
                              let uu____2472 =
                                let uu___209_2473 = fv in
                                let uu____2474 =
                                  let uu____2476 =
                                    let uu____2477 =
                                      let uu____2481 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2481) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2477 in
                                  Some uu____2476 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___209_2473.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___209_2473.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2474
                                } in
                              (uu____2472, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2464 in
                          FStar_All.pipe_left pos uu____2463
                      | uu____2500 -> p2 in
                    (env2, e, b, p3, false)) in
         let uu____2503 = aux [] env p in
         match uu____2503 with
         | (uu____2514,env1,b,p1,uu____2518) ->
             ((let uu____2524 = check_linear_pattern_variables p1 in
               FStar_All.pipe_left Prims.ignore uu____2524);
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
            let uu____2543 =
              let uu____2544 =
                let uu____2547 = FStar_ToSyntax_Env.qualify env x in
                (uu____2547, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2544 in
            (env, uu____2543, None) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2558 =
                  let uu____2559 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x in
                  FStar_Ident.id_of_text uu____2559 in
                mklet uu____2558
            | FStar_Parser_AST.PatVar (x,uu____2561) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2565);
                   FStar_Parser_AST.prange = uu____2566;_},t)
                ->
                let uu____2570 =
                  let uu____2571 =
                    let uu____2574 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2575 = desugar_term env t in
                    (uu____2574, uu____2575) in
                  LetBinder uu____2571 in
                (env, uu____2570, None)
            | uu____2577 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2583 = desugar_data_pat env p is_mut in
             match uu____2583 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2599 -> Some p1 in
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
  fun uu____2603  ->
    fun env  ->
      fun pat  ->
        let uu____2606 = desugar_data_pat env pat false in
        match uu____2606 with | (env1,uu____2613,pat1) -> (env1, pat1)
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
        let uu___210_2620 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___210_2620.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___210_2620.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___210_2620.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___210_2620.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___210_2620.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___210_2620.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___210_2620.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___210_2620.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___210_2620.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___210_2620.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___210_2620.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        } in
      desugar_term_maybe_top false env1 e
and desugar_typ:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___211_2624 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2624.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2624.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2624.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2624.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2624.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2624.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2624.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2624.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2624.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2624.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2624.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true
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
      fun uu____2627  ->
        fun range  ->
          match uu____2627 with
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
                let uu____2638 = FStar_ToSyntax_Env.try_lookup_lid env lid1 in
                match uu____2638 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2649 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1) in
                    failwith uu____2649 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range in
              let uu____2666 =
                let uu____2669 =
                  let uu____2670 =
                    let uu____2680 =
                      let uu____2686 =
                        let uu____2691 =
                          FStar_Syntax_Syntax.as_implicit false in
                        (repr1, uu____2691) in
                      [uu____2686] in
                    (lid2, uu____2680) in
                  FStar_Syntax_Syntax.Tm_app uu____2670 in
                FStar_Syntax_Syntax.mk uu____2669 in
              uu____2666 None range
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
            let uu____2726 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2726 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____2744 =
                    let uu____2745 =
                      let uu____2750 = mk_ref_read tm1 in
                      (uu____2750,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2745 in
                  FStar_All.pipe_left mk1 uu____2744
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2764 =
          let uu____2765 = unparen t in uu____2765.FStar_Parser_AST.tm in
        match uu____2764 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2766; FStar_Ident.ident = uu____2767;
              FStar_Ident.nsstr = uu____2768; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2770 ->
            let uu____2771 =
              let uu____2772 =
                let uu____2775 =
                  let uu____2776 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____2776 in
                (uu____2775, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2772 in
            Prims.raise uu____2771 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___212_2804 = e in
          {
            FStar_Syntax_Syntax.n = (uu___212_2804.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___212_2804.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___212_2804.FStar_Syntax_Syntax.vars)
          } in
        let uu____2811 =
          let uu____2812 = unparen top in uu____2812.FStar_Parser_AST.tm in
        match uu____2811 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2813 -> desugar_formula env top
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
        | FStar_Parser_AST.Op ("*",uu____2842::uu____2843::[]) when
            let uu____2845 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*" in
            FStar_All.pipe_right uu____2845 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2857 = flatten1 t1 in
                  FStar_List.append uu____2857 [t2]
              | uu____2859 -> [t] in
            let targs =
              let uu____2862 =
                let uu____2864 = unparen top in flatten1 uu____2864 in
              FStar_All.pipe_right uu____2862
                (FStar_List.map
                   (fun t  ->
                      let uu____2868 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____2868)) in
            let uu____2869 =
              let uu____2872 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2872 in
            (match uu____2869 with
             | (tup,uu____2879) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2882 =
              let uu____2885 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              Prims.fst uu____2885 in
            FStar_All.pipe_left setpos uu____2882
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2899 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____2899 with
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
                             let uu____2921 = desugar_term env t in
                             (uu____2921, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2928; FStar_Ident.ident = uu____2929;
              FStar_Ident.nsstr = uu____2930; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2932; FStar_Ident.ident = uu____2933;
              FStar_Ident.nsstr = uu____2934; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2936; FStar_Ident.ident = uu____2937;
               FStar_Ident.nsstr = uu____2938; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2948 =
              let uu____2949 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____2949 in
            mk1 uu____2948
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2950; FStar_Ident.ident = uu____2951;
              FStar_Ident.nsstr = uu____2952; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2954; FStar_Ident.ident = uu____2955;
              FStar_Ident.nsstr = uu____2956; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2958; FStar_Ident.ident = uu____2959;
              FStar_Ident.nsstr = uu____2960; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2964;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2965 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
            (match uu____2965 with
             | Some ed ->
                 let uu____2968 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange in
                 FStar_Syntax_Syntax.fvar uu____2968
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  ->
                 let uu____2969 =
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     (FStar_Ident.text_of_lid eff_name) txt in
                 failwith uu____2969)
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____2973 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____2973 with
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
              let uu____2989 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____2989 with
              | Some uu____2994 -> Some (true, l)
              | None  ->
                  let uu____2997 =
                    FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                  (match uu____2997 with
                   | Some new_name -> Some (false, new_name)
                   | uu____3005 -> None) in
            (match name with
             | Some (resolve,new_name) ->
                 let uu____3013 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     new_name i in
                 desugar_name mk1 setpos env resolve uu____3013
             | uu____3014 ->
                 let uu____3018 =
                   let uu____3019 =
                     let uu____3022 =
                       FStar_Util.format1
                         "Data constructor or effect %s not found"
                         l.FStar_Ident.str in
                     (uu____3022, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3019 in
                 Prims.raise uu____3018)
        | FStar_Parser_AST.Discrim lid ->
            let uu____3024 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
            (match uu____3024 with
             | None  ->
                 let uu____3026 =
                   let uu____3027 =
                     let uu____3030 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str in
                     (uu____3030, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3027 in
                 Prims.raise uu____3026
             | uu____3031 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 desugar_name mk1 setpos env true lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3042 = FStar_ToSyntax_Env.try_lookup_datacon env l in
            (match uu____3042 with
             | Some head1 ->
                 let uu____3045 =
                   let uu____3050 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                   (uu____3050, true) in
                 (match uu____3045 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3063 ->
                           let uu____3067 =
                             FStar_Util.take
                               (fun uu____3078  ->
                                  match uu____3078 with
                                  | (uu____3081,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args in
                           (match uu____3067 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3114  ->
                                       match uu____3114 with
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
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")),
                        (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3149 =
              FStar_List.fold_left
                (fun uu____3166  ->
                   fun b  ->
                     match uu____3166 with
                     | (env1,tparams,typs) ->
                         let uu____3197 = desugar_binder env1 b in
                         (match uu____3197 with
                          | (xopt,t1) ->
                              let uu____3213 =
                                match xopt with
                                | None  ->
                                    let uu____3218 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3218)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3213 with
                               | (env2,x) ->
                                   let uu____3230 =
                                     let uu____3232 =
                                       let uu____3234 =
                                         let uu____3235 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3235 in
                                       [uu____3234] in
                                     FStar_List.append typs uu____3232 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___213_3248 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___213_3248.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___213_3248.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3230))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3149 with
             | (env1,uu____3261,targs) ->
                 let uu____3273 =
                   let uu____3276 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3276 in
                 (match uu____3273 with
                  | (tup,uu____3283) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3291 = uncurry binders t in
            (match uu____3291 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___191_3314 =
                   match uu___191_3314 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3324 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3324
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3340 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3340 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3351 = desugar_binder env b in
            (match uu____3351 with
             | (None ,uu____3355) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3361 = as_binder env None b1 in
                 (match uu____3361 with
                  | ((x,uu____3365),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3370 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3370))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3385 =
              FStar_List.fold_left
                (fun uu____3392  ->
                   fun pat  ->
                     match uu____3392 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3407,t) ->
                              let uu____3409 =
                                let uu____3411 = free_type_vars env1 t in
                                FStar_List.append uu____3411 ftvs in
                              (env1, uu____3409)
                          | uu____3414 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3385 with
             | (uu____3417,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3425 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3425 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___192_3454 =
                   match uu___192_3454 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3483 =
                                 let uu____3484 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3484
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3483 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3526 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3526
                   | p::rest ->
                       let uu____3534 = desugar_binding_pat env1 p in
                       (match uu____3534 with
                        | (env2,b,pat) ->
                            let uu____3546 =
                              match b with
                              | LetBinder uu____3565 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3596) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3619 =
                                          let uu____3622 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3622, p1) in
                                        Some uu____3619
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3647,uu____3648) ->
                                             let tup2 =
                                               let uu____3650 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3650
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3654 =
                                                 let uu____3657 =
                                                   let uu____3658 =
                                                     let uu____3668 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____3671 =
                                                       let uu____3673 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____3674 =
                                                         let uu____3676 =
                                                           let uu____3677 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3677 in
                                                         [uu____3676] in
                                                       uu____3673 ::
                                                         uu____3674 in
                                                     (uu____3668, uu____3671) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3658 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3657 in
                                               uu____3654 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____3692 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3692 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3712,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3714,pats)) ->
                                             let tupn =
                                               let uu____3741 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3741
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3751 =
                                                 let uu____3752 =
                                                   let uu____3762 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____3765 =
                                                     let uu____3771 =
                                                       let uu____3777 =
                                                         let uu____3778 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3778 in
                                                       [uu____3777] in
                                                     FStar_List.append args
                                                       uu____3771 in
                                                   (uu____3762, uu____3765) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3752 in
                                               mk1 uu____3751 in
                                             let p2 =
                                               let uu____3793 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3793 in
                                             Some (sc1, p2)
                                         | uu____3817 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3546 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____3858,uu____3859,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3871 =
                let uu____3872 = unparen e in uu____3872.FStar_Parser_AST.tm in
              match uu____3871 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____3878 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____3881 ->
            let rec aux args e =
              let uu____3902 =
                let uu____3903 = unparen e in uu____3903.FStar_Parser_AST.tm in
              match uu____3902 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3913 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3913 in
                  aux (arg :: args) e1
              | uu____3920 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3931 =
              let uu____3932 =
                let uu____3937 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____3937,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____3932 in
            mk1 uu____3931
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____3967 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4009  ->
                        match uu____4009 with
                        | (p,def) ->
                            let uu____4023 = is_app_pattern p in
                            if uu____4023
                            then
                              let uu____4033 =
                                destruct_app_pattern env top_level p in
                              (uu____4033, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4062 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4062, def1)
                               | uu____4077 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4091);
                                           FStar_Parser_AST.prange =
                                             uu____4092;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4105 =
                                            let uu____4113 =
                                              let uu____4116 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4116 in
                                            (uu____4113, [], (Some t)) in
                                          (uu____4105, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4141)
                                        ->
                                        if top_level
                                        then
                                          let uu____4153 =
                                            let uu____4161 =
                                              let uu____4164 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4164 in
                                            (uu____4161, [], None) in
                                          (uu____4153, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4188 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4198 =
                FStar_List.fold_left
                  (fun uu____4222  ->
                     fun uu____4223  ->
                       match (uu____4222, uu____4223) with
                       | ((env1,fnames,rec_bindings),((f,uu____4267,uu____4268),uu____4269))
                           ->
                           let uu____4309 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4323 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4323 with
                                  | (env2,xx) ->
                                      let uu____4334 =
                                        let uu____4336 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4336 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4334))
                             | FStar_Util.Inr l ->
                                 let uu____4341 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4341, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4309 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4198 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4414 =
                    match uu____4414 with
                    | ((uu____4426,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4452 = is_comp_type env1 t in
                                if uu____4452
                                then
                                  ((let uu____4454 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4459 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4459)) in
                                    match uu____4454 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4462 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4463 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4463))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4462
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4468 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4468 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4471 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4481 =
                                let uu____4482 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4482
                                  None in
                              FStar_Util.Inr uu____4481 in
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
                  let uu____4502 =
                    let uu____4503 =
                      let uu____4511 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4511) in
                    FStar_Syntax_Syntax.Tm_let uu____4503 in
                  FStar_All.pipe_left mk1 uu____4502 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4538 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4538 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4559 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4559 None in
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
                    | LocalBinder (x,uu____4567) ->
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
                              let uu____4576 =
                                let uu____4579 =
                                  let uu____4580 =
                                    let uu____4596 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4597 =
                                      let uu____4599 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1) in
                                      [uu____4599] in
                                    (uu____4596, uu____4597) in
                                  FStar_Syntax_Syntax.Tm_match uu____4580 in
                                FStar_Syntax_Syntax.mk uu____4579 in
                              uu____4576 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4614 =
                          let uu____4615 =
                            let uu____4623 =
                              let uu____4624 =
                                let uu____4625 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4625] in
                              FStar_Syntax_Subst.close uu____4624 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4623) in
                          FStar_Syntax_Syntax.Tm_let uu____4615 in
                        FStar_All.pipe_left mk1 uu____4614 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____4645 = is_rec || (is_app_pattern pat) in
            if uu____4645
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____4651 =
              let uu____4652 =
                let uu____4668 = desugar_term env t1 in
                let uu____4669 =
                  let uu____4679 =
                    let uu____4688 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____4691 = desugar_term env t2 in
                    (uu____4688, None, uu____4691) in
                  let uu____4699 =
                    let uu____4709 =
                      let uu____4718 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____4721 = desugar_term env t3 in
                      (uu____4718, None, uu____4721) in
                    [uu____4709] in
                  uu____4679 :: uu____4699 in
                (uu____4668, uu____4669) in
              FStar_Syntax_Syntax.Tm_match uu____4652 in
            mk1 uu____4651
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
            let desugar_branch uu____4807 =
              match uu____4807 with
              | (pat,wopt,b) ->
                  let uu____4817 = desugar_match_pat env pat in
                  (match uu____4817 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4826 = desugar_term env1 e1 in
                             Some uu____4826 in
                       let b1 = desugar_term env1 b in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1)) in
            let uu____4829 =
              let uu____4830 =
                let uu____4846 = desugar_term env e in
                let uu____4847 = FStar_List.map desugar_branch branches in
                (uu____4846, uu____4847) in
              FStar_Syntax_Syntax.Tm_match uu____4830 in
            FStar_All.pipe_left mk1 uu____4829
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____4866 = is_comp_type env t in
              if uu____4866
              then
                let uu____4871 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____4871
              else
                (let uu____4877 = desugar_term env t in
                 FStar_Util.Inl uu____4877) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____4882 =
              let uu____4883 =
                let uu____4901 = desugar_term env e in
                (uu____4901, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____4883 in
            FStar_All.pipe_left mk1 uu____4882
        | FStar_Parser_AST.Record (uu____4917,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____4938 = FStar_List.hd fields in
              match uu____4938 with | (f,uu____4945) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4969  ->
                        match uu____4969 with
                        | (g,uu____4973) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____4977,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4985 =
                         let uu____4986 =
                           let uu____4989 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____4989, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____4986 in
                       Prims.raise uu____4985
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
                  let uu____4995 =
                    let uu____5001 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5015  ->
                              match uu____5015 with
                              | (f,uu____5021) ->
                                  let uu____5022 =
                                    let uu____5023 = get_field None f in
                                    FStar_All.pipe_left Prims.snd uu____5023 in
                                  (uu____5022, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5001) in
                  FStar_Parser_AST.Construct uu____4995
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5034 =
                      let uu____5035 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5035 in
                    FStar_Parser_AST.mk_term uu____5034 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5037 =
                      let uu____5044 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5058  ->
                                match uu____5058 with
                                | (f,uu____5064) -> get_field (Some xterm) f)) in
                      (None, uu____5044) in
                    FStar_Parser_AST.Record uu____5037 in
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
                         FStar_Syntax_Syntax.tk = uu____5080;
                         FStar_Syntax_Syntax.pos = uu____5081;
                         FStar_Syntax_Syntax.vars = uu____5082;_},args);
                    FStar_Syntax_Syntax.tk = uu____5084;
                    FStar_Syntax_Syntax.pos = uu____5085;
                    FStar_Syntax_Syntax.vars = uu____5086;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5108 =
                     let uu____5109 =
                       let uu____5119 =
                         let uu____5120 =
                           let uu____5122 =
                             let uu____5123 =
                               let uu____5127 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5127) in
                             FStar_Syntax_Syntax.Record_ctor uu____5123 in
                           Some uu____5122 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5120 in
                       (uu____5119, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5109 in
                   FStar_All.pipe_left mk1 uu____5108 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5151 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5154 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
            (match uu____5154 with
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
                 let uu____5167 =
                   let uu____5168 =
                     let uu____5178 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual1 in
                     let uu____5179 =
                       let uu____5181 = FStar_Syntax_Syntax.as_arg e1 in
                       [uu____5181] in
                     (uu____5178, uu____5179) in
                   FStar_Syntax_Syntax.Tm_app uu____5168 in
                 FStar_All.pipe_left mk1 uu____5167)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5187 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5188 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5189,uu____5190,uu____5191) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5198,uu____5199,uu____5200) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5207,uu____5208,uu____5209) ->
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
           (fun uu____5233  ->
              match uu____5233 with
              | (a,imp) ->
                  let uu____5241 = desugar_term env a in
                  arg_withimp_e imp uu____5241))
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
        let is_requires uu____5258 =
          match uu____5258 with
          | (t1,uu____5262) ->
              let uu____5263 =
                let uu____5264 = unparen t1 in uu____5264.FStar_Parser_AST.tm in
              (match uu____5263 with
               | FStar_Parser_AST.Requires uu____5265 -> true
               | uu____5269 -> false) in
        let is_ensures uu____5275 =
          match uu____5275 with
          | (t1,uu____5279) ->
              let uu____5280 =
                let uu____5281 = unparen t1 in uu____5281.FStar_Parser_AST.tm in
              (match uu____5280 with
               | FStar_Parser_AST.Ensures uu____5282 -> true
               | uu____5286 -> false) in
        let is_app head1 uu____5295 =
          match uu____5295 with
          | (t1,uu____5299) ->
              let uu____5300 =
                let uu____5301 = unparen t1 in uu____5301.FStar_Parser_AST.tm in
              (match uu____5300 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5303;
                      FStar_Parser_AST.level = uu____5304;_},uu____5305,uu____5306)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5307 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5325 = head_and_args t1 in
          match uu____5325 with
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
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Requires
                            ((FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Name
                                   FStar_Syntax_Const.true_lid)
                                t1.FStar_Parser_AST.range
                                FStar_Parser_AST.Formula), None))
                         t1.FStar_Parser_AST.range
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
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         [unit_tm; req; ens; nil_pat]
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         [unit_tm; req_true; ens; nil_pat; dec]
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_app "decreases" dec)
                         -> [unit_tm; req; ens; nil_pat; dec]
                     | more -> unit_tm :: more in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5490 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5490, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5504 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5504
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5513 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5513
                      FStar_Syntax_Const.prims_lid)
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
               | uu____5533 ->
                   let default_effect =
                     let uu____5535 = FStar_Options.ml_ish () in
                     if uu____5535
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____5538 =
                           FStar_Options.warn_default_effects () in
                         if uu____5538
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____5551 = pre_process_comp_typ t in
        match uu____5551 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5581 =
                  let uu____5582 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5582 in
                fail uu____5581)
             else ();
             (let is_universe uu____5589 =
                match uu____5589 with
                | (uu____5592,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____5594 = FStar_Util.take is_universe args in
              match uu____5594 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5625  ->
                         match uu____5625 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____5630 =
                    let uu____5638 = FStar_List.hd args1 in
                    let uu____5643 = FStar_List.tl args1 in
                    (uu____5638, uu____5643) in
                  (match uu____5630 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____5674 =
                         FStar_All.pipe_right rest1
                           (FStar_List.partition
                              (fun uu____5712  ->
                                 match uu____5712 with
                                 | (t1,uu____5719) ->
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____5727;
                                             FStar_Syntax_Syntax.pos =
                                               uu____5728;
                                             FStar_Syntax_Syntax.vars =
                                               uu____5729;_},uu____5730::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____5752 -> false))) in
                       (match uu____5674 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5795  ->
                                      match uu____5795 with
                                      | (t1,uu____5802) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5809,(arg,uu____5811)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5833 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5845 -> false in
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
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_succ
                                                      FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 let uu____5937 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____5937
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____5949 -> pat in
                                         let uu____5950 =
                                           let uu____5957 =
                                             let uu____5964 =
                                               let uu____5970 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____5970, aq) in
                                             [uu____5964] in
                                           ens :: uu____5957 in
                                         req :: uu____5950
                                     | uu____6006 -> rest2
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
        | uu____6022 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let pos t = t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___214_6063 = t in
        {
          FStar_Syntax_Syntax.n = (uu___214_6063.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___214_6063.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___214_6063.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___215_6093 = b in
             {
               FStar_Parser_AST.b = (uu___215_6093.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___215_6093.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___215_6093.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6126 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6126)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6135 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6135 with
             | (env1,a1) ->
                 let a2 =
                   let uu___216_6143 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___216_6143.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___216_6143.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6156 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6165 =
                     let uu____6168 =
                       let uu____6172 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6172] in
                     no_annot_abs uu____6168 body2 in
                   FStar_All.pipe_left setpos uu____6165 in
                 let uu____6177 =
                   let uu____6178 =
                     let uu____6188 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6189 =
                       let uu____6191 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6191] in
                     (uu____6188, uu____6189) in
                   FStar_Syntax_Syntax.Tm_app uu____6178 in
                 FStar_All.pipe_left mk1 uu____6177)
        | uu____6195 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6244 = q (rest, pats, body) in
              let uu____6248 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6244 uu____6248
                FStar_Parser_AST.Formula in
            let uu____6249 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6249 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6254 -> failwith "impossible" in
      let uu____6256 =
        let uu____6257 = unparen f in uu____6257.FStar_Parser_AST.tm in
      match uu____6256 with
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
          let uu____6287 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6287
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6308 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6308
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6333 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6337 =
        FStar_List.fold_left
          (fun uu____6350  ->
             fun b  ->
               match uu____6350 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___217_6378 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___217_6378.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___217_6378.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___217_6378.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6388 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6388 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___218_6400 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___218_6400.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___218_6400.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6409 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6337 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6459 = desugar_typ env t in ((Some x), uu____6459)
      | FStar_Parser_AST.TVariable x ->
          let uu____6462 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6462)
      | FStar_Parser_AST.NoName t ->
          let uu____6477 = desugar_typ env t in (None, uu____6477)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___193_6526  ->
            match uu___193_6526 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6527 -> false)) in
  let quals2 q =
    let uu____6535 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface in
    if uu____6535
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1 in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d in
          let uu____6542 =
            let uu____6543 =
              let uu____6549 =
                quals2
                  [FStar_Syntax_Syntax.OnlyName;
                  FStar_Syntax_Syntax.Discriminator d] in
              (disc_name, [], FStar_Syntax_Syntax.tun, uu____6549) in
            FStar_Syntax_Syntax.Sig_declare_typ uu____6543 in
          {
            FStar_Syntax_Syntax.sigel = uu____6542;
            FStar_Syntax_Syntax.sigdoc = None;
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
            let uu____6574 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6584  ->
                        match uu____6584 with
                        | (x,uu____6589) ->
                            let uu____6590 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____6590 with
                             | (field_name,uu____6595) ->
                                 let only_decl =
                                   ((let uu____6597 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6597)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6598 =
                                        let uu____6599 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____6599.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____6598) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6609 =
                                       FStar_List.filter
                                         (fun uu___194_6611  ->
                                            match uu___194_6611 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6612 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6609
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___195_6620  ->
                                             match uu___195_6620 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6621 -> false)) in
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
                                     FStar_Syntax_Syntax.sigdoc = None;
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name)
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6628 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____6628
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____6632 =
                                        let uu____6635 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____6635 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6632;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____6637 =
                                        let uu____6638 =
                                          let uu____6646 =
                                            let uu____6648 =
                                              let uu____6649 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____6649
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____6648] in
                                          ((false, [lb]), uu____6646, quals1,
                                            []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6638 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6637;
                                        FStar_Syntax_Syntax.sigdoc = None;
                                        FStar_Syntax_Syntax.sigrng = p
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____6574 FStar_List.flatten
let mk_data_projector_names iquals env uu____6689 =
  match uu____6689 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6697,t,uu____6699,n1,quals,uu____6702) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6707 = FStar_Syntax_Util.arrow_formals t in
           (match uu____6707 with
            | (formals,uu____6717) ->
                (match formals with
                 | [] -> []
                 | uu____6731 ->
                     let filter_records uu___196_6739 =
                       match uu___196_6739 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6741,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6748 -> None in
                     let fv_qual =
                       let uu____6750 =
                         FStar_Util.find_map quals filter_records in
                       match uu____6750 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals in
                     let uu____6757 = FStar_Util.first_N n1 formals in
                     (match uu____6757 with
                      | (uu____6769,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6783 -> [])
let mk_typ_abbrev:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range ->
                  FStar_Syntax_Syntax.fsdoc Prims.option ->
                    FStar_Syntax_Syntax.sigelt
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  fun doc1  ->
                    let dd =
                      let uu____6826 =
                        FStar_All.pipe_right quals
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                      if uu____6826
                      then
                        let uu____6828 =
                          FStar_Syntax_Util.incr_delta_qualifier t in
                        FStar_Syntax_Syntax.Delta_abstract uu____6828
                      else FStar_Syntax_Util.incr_delta_qualifier t in
                    let lb =
                      let uu____6831 =
                        let uu____6834 =
                          FStar_Syntax_Syntax.lid_as_fv lid dd None in
                        FStar_Util.Inr uu____6834 in
                      let uu____6835 =
                        let uu____6838 = FStar_Syntax_Syntax.mk_Total k in
                        FStar_Syntax_Util.arrow typars uu____6838 in
                      let uu____6841 = no_annot_abs typars t in
                      {
                        FStar_Syntax_Syntax.lbname = uu____6831;
                        FStar_Syntax_Syntax.lbunivs = uvs;
                        FStar_Syntax_Syntax.lbtyp = uu____6835;
                        FStar_Syntax_Syntax.lbeff =
                          FStar_Syntax_Const.effect_Tot_lid;
                        FStar_Syntax_Syntax.lbdef = uu____6841
                      } in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_let
                           ((false, [lb]), lids, quals, []));
                      FStar_Syntax_Syntax.sigdoc = doc1;
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
          let tycon_id uu___197_6875 =
            match uu___197_6875 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6914 =
                  let uu____6915 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____6915 in
                FStar_Parser_AST.mk_term uu____6914 x.FStar_Ident.idRange
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
              | uu____6937 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____6940 =
                     let uu____6941 =
                       let uu____6945 = binder_to_term b in
                       (out, uu____6945, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____6941 in
                   FStar_Parser_AST.mk_term uu____6940
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___198_6952 =
            match uu___198_6952 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____6981  ->
                       match uu____6981 with
                       | (x,t,uu____6988) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____6992 =
                    let uu____6993 =
                      let uu____6994 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____6994 in
                    FStar_Parser_AST.mk_term uu____6993
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____6992 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____6997 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7009  ->
                          match uu____7009 with
                          | (x,uu____7015,uu____7016) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____6997)
            | uu____7043 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___199_7065 =
            match uu___199_7065 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7079 = typars_of_binders _env binders in
                (match uu____7079 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7107 =
                         let uu____7108 =
                           let uu____7109 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7109 in
                         FStar_Parser_AST.mk_term uu____7108
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7107 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, [], quals1));
                         FStar_Syntax_Syntax.sigdoc =
                           (d.FStar_Parser_AST.doc);
                         FStar_Syntax_Syntax.sigrng = rng
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____7120 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7146 =
              FStar_List.fold_left
                (fun uu____7162  ->
                   fun uu____7163  ->
                     match (uu____7162, uu____7163) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7211 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7211 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7146 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7272 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7272
                | uu____7273 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7278 = desugar_abstract_tc quals env [] tc in
              (match uu____7278 with
               | (uu____7285,uu____7286,se,uu____7288) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7291,typars,k,[],[],quals1) ->
                         let quals2 =
                           let uu____7301 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7301
                           then quals1
                           else
                             ((let uu____7306 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7307 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7306 uu____7307);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7311 ->
                               let uu____7312 =
                                 let uu____7315 =
                                   let uu____7316 =
                                     let uu____7324 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7324) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7316 in
                                 FStar_Syntax_Syntax.mk uu____7315 in
                               uu____7312 None se.FStar_Syntax_Syntax.sigrng in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (l, [], t, quals2));
                           FStar_Syntax_Syntax.sigdoc = None;
                           FStar_Syntax_Syntax.sigrng =
                             (se.FStar_Syntax_Syntax.sigrng)
                         }
                     | uu____7335 -> se in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7346 = typars_of_binders env binders in
              (match uu____7346 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7366 =
                           FStar_Util.for_some
                             (fun uu___200_7367  ->
                                match uu___200_7367 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7368 -> false) quals in
                         if uu____7366
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7374 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___201_7376  ->
                               match uu___201_7376 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7377 -> false)) in
                     if uu____7374
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let se =
                     let uu____7383 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7383
                     then
                       let uu____7385 =
                         let uu____7389 =
                           let uu____7390 = unparen t in
                           uu____7390.FStar_Parser_AST.tm in
                         match uu____7389 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7402 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7418)::args_rev ->
                                   let uu____7425 =
                                     let uu____7426 = unparen last_arg in
                                     uu____7426.FStar_Parser_AST.tm in
                                   (match uu____7425 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7441 -> ([], args))
                               | uu____7446 -> ([], args) in
                             (match uu____7402 with
                              | (cattributes,args1) ->
                                  let uu____7467 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7467))
                         | uu____7473 -> (t, []) in
                       match uu____7385 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let uu____7484 =
                             let uu____7485 =
                               let uu____7494 =
                                 FStar_ToSyntax_Env.qualify env id in
                               let uu____7495 =
                                 FStar_All.pipe_right quals1
                                   (FStar_List.filter
                                      (fun uu___202_7499  ->
                                         match uu___202_7499 with
                                         | FStar_Syntax_Syntax.Effect  ->
                                             false
                                         | uu____7500 -> true)) in
                               (uu____7494, [], typars1, c1, uu____7495,
                                 (FStar_List.append cattributes
                                    (FStar_Syntax_Util.comp_flags c1))) in
                             FStar_Syntax_Syntax.Sig_effect_abbrev uu____7485 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____7484;
                             FStar_Syntax_Syntax.sigdoc =
                               (d.FStar_Parser_AST.doc);
                             FStar_Syntax_Syntax.sigrng = rng
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        let nm = FStar_ToSyntax_Env.qualify env id in
                        mk_typ_abbrev nm [] typars k t1 [nm] quals1 rng
                          d.FStar_Parser_AST.doc) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7509)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7522 = tycon_record_as_variant trec in
              (match uu____7522 with
               | (t,fs) ->
                   let uu____7532 =
                     let uu____7534 =
                       let uu____7535 =
                         let uu____7540 =
                           let uu____7542 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7542 in
                         (uu____7540, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7535 in
                     uu____7534 :: quals in
                   desugar_tycon env d uu____7532 [t])
          | uu____7545::uu____7546 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____7633 = et in
                match uu____7633 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7747 ->
                         let trec = tc in
                         let uu____7760 = tycon_record_as_variant trec in
                         (match uu____7760 with
                          | (t,fs) ->
                              let uu____7791 =
                                let uu____7793 =
                                  let uu____7794 =
                                    let uu____7799 =
                                      let uu____7801 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____7801 in
                                    (uu____7799, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____7794 in
                                uu____7793 :: quals1 in
                              collect_tcs uu____7791 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7847 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____7847 with
                          | (env2,uu____7878,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____7956 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____7956 with
                          | (env2,uu____7987,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8051 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8075 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8075 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___204_8313  ->
                             match uu___204_8313 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8345,uu____8346,uu____8347);
                                    FStar_Syntax_Syntax.sigdoc = uu____8348;
                                    FStar_Syntax_Syntax.sigrng = uu____8349;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8383 =
                                     typars_of_binders env1 binders in
                                   match uu____8383 with
                                   | (env2,tpars1) ->
                                       let uu____8400 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8400 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8419 =
                                   let uu____8426 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng d.FStar_Parser_AST.doc in
                                   ([], uu____8426) in
                                 [uu____8419]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8451,tags);
                                    FStar_Syntax_Syntax.sigdoc = uu____8453;
                                    FStar_Syntax_Syntax.sigrng = uu____8454;_},constrs,tconstr,quals1)
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
                                 let uu____8508 = push_tparams env1 tpars in
                                 (match uu____8508 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8543  ->
                                             match uu____8543 with
                                             | (x,uu____8551) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____8556 =
                                        let uu____8567 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8607  ->
                                                  match uu____8607 with
                                                  | (id,topt,uu____8624,of_notation)
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
                                                        let uu____8636 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____8636 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___203_8642
                                                                 ->
                                                                match uu___203_8642
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8649
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____8655 =
                                                        let uu____8662 =
                                                          let uu____8663 =
                                                            let uu____8664 =
                                                              let uu____8674
                                                                =
                                                                let uu____8677
                                                                  =
                                                                  let uu____8680
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____8680 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____8677 in
                                                              (name, univs,
                                                                uu____8674,
                                                                tname, ntps,
                                                                quals2,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____8664 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____8663;
                                                            FStar_Syntax_Syntax.sigdoc
                                                              =
                                                              (d.FStar_Parser_AST.doc);
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng
                                                          } in
                                                        (tps, uu____8662) in
                                                      (name, uu____8655))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8567 in
                                      (match uu____8556 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames,
                                                      tags));
                                               FStar_Syntax_Syntax.sigdoc =
                                                 (d.FStar_Parser_AST.doc);
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng
                                             })
                                           :: constrs1))
                             | uu____8765 -> failwith "impossible")) in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd) in
                   let uu____8813 =
                     let uu____8817 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____8817 rng d.FStar_Parser_AST.doc in
                   (match uu____8813 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (mk_data_projector_names quals env3)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____8854,tps,k,uu____8857,constrs,quals1)
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
                                  | uu____8873 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        (env4,
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
      let uu____8891 =
        FStar_List.fold_left
          (fun uu____8898  ->
             fun b  ->
               match uu____8898 with
               | (env1,binders1) ->
                   let uu____8910 = desugar_binder env1 b in
                   (match uu____8910 with
                    | (Some a,k) ->
                        let uu____8920 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____8920 with
                         | (env2,a1) ->
                             let uu____8928 =
                               let uu____8930 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___219_8931 = a1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___219_8931.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___219_8931.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    }) in
                               uu____8930 :: binders1 in
                             (env2, uu____8928))
                    | uu____8933 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____8891 with
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
                let uu____9011 = desugar_binders monad_env eff_binders in
                match uu____9011 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9024 =
                        let uu____9025 =
                          let uu____9029 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          Prims.fst uu____9029 in
                        FStar_List.length uu____9025 in
                      uu____9024 = (Prims.parse_int "1") in
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
                          (uu____9057,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9059,uu____9060,uu____9061),uu____9062)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9079 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9080 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9086 = name_of_eff_decl decl in
                           FStar_List.mem uu____9086 mandatory_members)
                        eff_decls in
                    (match uu____9080 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9096 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9107  ->
                                   fun decl  ->
                                     match uu____9107 with
                                     | (env2,out) ->
                                         let uu____9119 =
                                           desugar_decl env2 decl in
                                         (match uu____9119 with
                                          | (env3,ses) ->
                                              let uu____9127 =
                                                let uu____9129 =
                                                  FStar_List.hd ses in
                                                uu____9129 :: out in
                                              (env3, uu____9127))) (env1, [])) in
                         (match uu____9096 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions1 =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9145,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9147,uu____9148,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9149,
                                                               (def,uu____9151)::
                                                               (cps_type,uu____9153)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9154;
                                                            FStar_Parser_AST.level
                                                              = uu____9155;_}),uu____9156)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9182 =
                                              FStar_ToSyntax_Env.qualify env2
                                                name in
                                            let uu____9183 =
                                              let uu____9184 =
                                                desugar_term env2 def in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9184 in
                                            let uu____9185 =
                                              let uu____9186 =
                                                desugar_typ env2 cps_type in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9186 in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                = uu____9182;
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                = name;
                                              FStar_Syntax_Syntax.action_univs
                                                = [];
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____9183;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____9185
                                            }
                                        | FStar_Parser_AST.Tycon
                                            (uu____9187,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9189,uu____9190,defn),uu____9192)::[])
                                            when for_free ->
                                            let uu____9209 =
                                              FStar_ToSyntax_Env.qualify env2
                                                name in
                                            let uu____9210 =
                                              let uu____9211 =
                                                desugar_term env2 defn in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9211 in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                = uu____9209;
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                = name;
                                              FStar_Syntax_Syntax.action_univs
                                                = [];
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____9210;
                                              FStar_Syntax_Syntax.action_typ
                                                = FStar_Syntax_Syntax.tun
                                            }
                                        | uu____9212 ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____9222 =
                                  let uu____9223 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9223 in
                                ([], uu____9222) in
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
                                    let uu____9235 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____9235) in
                                  let uu____9245 =
                                    let uu____9246 =
                                      let uu____9247 =
                                        let uu____9248 = lookup "repr" in
                                        Prims.snd uu____9248 in
                                      let uu____9253 = lookup "return" in
                                      let uu____9254 = lookup "bind" in
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
                                        FStar_Syntax_Syntax.repr = uu____9247;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9253;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9254;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9246 in
                                  sigelt_of_decl d uu____9245
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___205_9257  ->
                                          match uu___205_9257 with
                                          | FStar_Syntax_Syntax.Reifiable 
                                            |FStar_Syntax_Syntax.Reflectable
                                            _ -> true
                                          | uu____9259 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9265 =
                                     let uu____9266 =
                                       let uu____9267 = lookup "return_wp" in
                                       let uu____9268 = lookup "bind_wp" in
                                       let uu____9269 = lookup "if_then_else" in
                                       let uu____9270 = lookup "ite_wp" in
                                       let uu____9271 = lookup "stronger" in
                                       let uu____9272 = lookup "close_wp" in
                                       let uu____9273 = lookup "assert_p" in
                                       let uu____9274 = lookup "assume_p" in
                                       let uu____9275 = lookup "null_wp" in
                                       let uu____9276 = lookup "trivial" in
                                       let uu____9277 =
                                         if rr
                                         then
                                           let uu____9278 = lookup "repr" in
                                           FStar_All.pipe_left Prims.snd
                                             uu____9278
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____9287 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____9289 =
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
                                           uu____9267;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9268;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9269;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9270;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9271;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9272;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9273;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9274;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9275;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9276;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9277;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9287;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9289;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9266 in
                                   sigelt_of_decl d uu____9265) in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se in
                              let env4 =
                                FStar_All.pipe_right actions1
                                  (FStar_List.fold_left
                                     (fun env4  ->
                                        fun a  ->
                                          let uu____9296 =
                                            FStar_Syntax_Util.action_as_lb
                                              mname a in
                                          FStar_ToSyntax_Env.push_sigelt env4
                                            uu____9296) env3) in
                              let env5 =
                                let uu____9298 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____9298
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env) in
                                  let refl_decl =
                                    sigelt_of_decl d
                                      (FStar_Syntax_Syntax.Sig_declare_typ
                                         (reflect_lid, [],
                                           FStar_Syntax_Syntax.tun,
                                           [FStar_Syntax_Syntax.Assumption;
                                           FStar_Syntax_Syntax.Reflectable
                                             mname])) in
                                  FStar_ToSyntax_Env.push_sigelt env4
                                    refl_decl
                                else env4 in
                              (env5, [se])))
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
                let uu____9321 = desugar_binders env1 eff_binders in
                match uu____9321 with
                | (env2,binders) ->
                    let uu____9332 =
                      let uu____9341 = head_and_args defn in
                      match uu____9341 with
                      | (head1,args) ->
                          let ed =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l ->
                                FStar_ToSyntax_Env.fail_or env2
                                  (FStar_ToSyntax_Env.try_lookup_effect_defn
                                     env2) l
                            | uu____9365 ->
                                let uu____9366 =
                                  let uu____9367 =
                                    let uu____9370 =
                                      let uu____9371 =
                                        let uu____9372 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____9372 " not found" in
                                      Prims.strcat "Effect " uu____9371 in
                                    (uu____9370, (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____9367 in
                                Prims.raise uu____9366 in
                          let uu____9373 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9389)::args_rev ->
                                let uu____9396 =
                                  let uu____9397 = unparen last_arg in
                                  uu____9397.FStar_Parser_AST.tm in
                                (match uu____9396 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____9412 -> ([], args))
                            | uu____9417 -> ([], args) in
                          (match uu____9373 with
                           | (cattributes,args1) ->
                               let uu____9443 = desugar_args env2 args1 in
                               let uu____9448 =
                                 desugar_attributes env2 cattributes in
                               (ed, uu____9443, uu____9448)) in
                    (match uu____9332 with
                     | (ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____9481 =
                           match uu____9481 with
                           | (uu____9488,x) ->
                               let uu____9492 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____9492 with
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
                                      let uu____9512 =
                                        let uu____9513 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____9513 in
                                      ([], uu____9512)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____9517 =
                             let uu____9519 = trans_qual1 (Some mname) in
                             FStar_List.map uu____9519 quals in
                           let uu____9522 =
                             let uu____9523 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             Prims.snd uu____9523 in
                           let uu____9529 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____9530 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____9531 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____9532 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____9533 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____9534 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____9535 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____9536 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____9537 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____9538 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____9539 =
                             let uu____9540 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             Prims.snd uu____9540 in
                           let uu____9546 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____9547 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____9548 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____9551 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____9552 =
                                    let uu____9553 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    Prims.snd uu____9553 in
                                  let uu____9559 =
                                    let uu____9560 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    Prims.snd uu____9560 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____9551;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____9552;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____9559
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.qualifiers = uu____9517;
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____9522;
                             FStar_Syntax_Syntax.ret_wp = uu____9529;
                             FStar_Syntax_Syntax.bind_wp = uu____9530;
                             FStar_Syntax_Syntax.if_then_else = uu____9531;
                             FStar_Syntax_Syntax.ite_wp = uu____9532;
                             FStar_Syntax_Syntax.stronger = uu____9533;
                             FStar_Syntax_Syntax.close_wp = uu____9534;
                             FStar_Syntax_Syntax.assert_p = uu____9535;
                             FStar_Syntax_Syntax.assume_p = uu____9536;
                             FStar_Syntax_Syntax.null_wp = uu____9537;
                             FStar_Syntax_Syntax.trivial = uu____9538;
                             FStar_Syntax_Syntax.repr = uu____9539;
                             FStar_Syntax_Syntax.return_repr = uu____9546;
                             FStar_Syntax_Syntax.bind_repr = uu____9547;
                             FStar_Syntax_Syntax.actions = uu____9548
                           } in
                         let se =
                           let for_free =
                             let uu____9568 =
                               let uu____9569 =
                                 let uu____9573 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 Prims.fst uu____9573 in
                               FStar_List.length uu____9569 in
                             uu____9568 = (Prims.parse_int "1") in
                           sigelt_of_decl d
                             (if for_free
                              then
                                FStar_Syntax_Syntax.Sig_new_effect_for_free
                                  ed1
                              else FStar_Syntax_Syntax.Sig_new_effect ed1) in
                         let monad_env = env2 in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se in
                         let env4 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env4  ->
                                   fun a  ->
                                     let uu____9598 =
                                       FStar_Syntax_Util.action_as_lb mname a in
                                     FStar_ToSyntax_Env.push_sigelt env4
                                       uu____9598) env3) in
                         let env5 =
                           let uu____9600 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____9600
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env) in
                             let refl_decl =
                               sigelt_of_decl d
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (reflect_lid, [],
                                      FStar_Syntax_Syntax.tun,
                                      [FStar_Syntax_Syntax.Assumption;
                                      FStar_Syntax_Syntax.Reflectable mname])) in
                             FStar_ToSyntax_Env.push_sigelt env4 refl_decl
                           else env4 in
                         (env5, [se]))
and desugar_decl:
  env_t -> FStar_Parser_AST.decl -> (env_t* FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            sigelt_of_decl d
              (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p)) in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____9625 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____9637 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____9637, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____9658  -> match uu____9658 with | (x,uu____9663) -> x)
              tcs in
          let uu____9666 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____9666 tcs1
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
               | (p,uu____9705)::[] ->
                   let uu____9710 = is_app_pattern p in
                   Prims.op_Negation uu____9710
               | uu____9711 -> false) in
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
            let uu____9722 =
              let uu____9723 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____9723.FStar_Syntax_Syntax.n in
            (match uu____9722 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____9729) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____9749::uu____9750 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____9752 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___206_9756  ->
                               match uu___206_9756 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____9758;
                                   FStar_Syntax_Syntax.lbunivs = uu____9759;
                                   FStar_Syntax_Syntax.lbtyp = uu____9760;
                                   FStar_Syntax_Syntax.lbeff = uu____9761;
                                   FStar_Syntax_Syntax.lbdef = uu____9762;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____9769;
                                   FStar_Syntax_Syntax.lbtyp = uu____9770;
                                   FStar_Syntax_Syntax.lbeff = uu____9771;
                                   FStar_Syntax_Syntax.lbdef = uu____9772;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____9784 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____9790  ->
                             match uu____9790 with
                             | (uu____9793,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____9784
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____9801 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____9801
                   then
                     let uu____9806 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___220_9813 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___221_9814 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___221_9814.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___221_9814.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___220_9813.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___220_9813.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___220_9813.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___220_9813.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((Prims.fst lbs), uu____9806)
                   else lbs in
                 let s =
                   let uu____9822 =
                     let uu____9823 =
                       let uu____9831 =
                         FStar_All.pipe_right fvs
                           (FStar_List.map
                              (fun fv  ->
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                       (lbs1, uu____9831, quals2, attrs1) in
                     FStar_Syntax_Syntax.Sig_let uu____9823 in
                   sigelt_of_decl d uu____9822 in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 (env1, [s])
             | uu____9848 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____9852 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____9863 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____9852 with
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
                       let uu___222_9879 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___222_9879.FStar_Parser_AST.prange)
                       }
                   | uu____9880 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___223_9884 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___223_9884.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___223_9884.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___223_9884.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____9903 id =
                   match uu____9903 with
                   | (env1,ses) ->
                       let main =
                         let uu____9916 =
                           let uu____9917 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____9917 in
                         FStar_Parser_AST.mk_term uu____9916
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
                       let uu____9945 = desugar_decl env1 id_decl in
                       (match uu____9945 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____9956 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____9956 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se = sigelt_of_decl d (FStar_Syntax_Syntax.Sig_main e) in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t in
          let uu____9970 =
            let uu____9972 =
              let uu____9973 =
                let uu____9974 =
                  let uu____9979 = FStar_ToSyntax_Env.qualify env id in
                  (uu____9979, f, [FStar_Syntax_Syntax.Assumption]) in
                FStar_Syntax_Syntax.Sig_assume uu____9974 in
              sigelt_of_decl d uu____9973 in
            [uu____9972] in
          (env, uu____9970)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____9986 = close_fun env t in desugar_term env uu____9986 in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let se =
            let uu____9992 =
              let uu____9993 =
                let uu____9999 = FStar_ToSyntax_Env.qualify env id in
                let uu____10000 = FStar_List.map (trans_qual1 None) quals1 in
                (uu____9999, [], t1, uu____10000) in
              FStar_Syntax_Syntax.Sig_declare_typ uu____9993 in
            sigelt_of_decl d uu____9992 in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in (env1, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10008 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10008 with
           | (t,uu____10016) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let se =
                 sigelt_of_decl d
                   (FStar_Syntax_Syntax.Sig_datacon
                      (l, [], t, FStar_Syntax_Const.exn_lid,
                        (Prims.parse_int "0"),
                        [FStar_Syntax_Syntax.ExceptionConstructor],
                        [FStar_Syntax_Const.exn_lid])) in
               let se' =
                 sigelt_of_decl d
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l])) in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
               let data_ops = mk_data_projector_names [] env1 ([], se) in
               let discs =
                 mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l] in
               let env2 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
                   (FStar_List.append discs data_ops) in
               (env2, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____10043 =
              let uu____10047 = FStar_Syntax_Syntax.null_binder t in
              [uu____10047] in
            let uu____10048 =
              let uu____10051 =
                let uu____10052 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                Prims.fst uu____10052 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10051 in
            FStar_Syntax_Util.arrow uu____10043 uu____10048 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let se =
            sigelt_of_decl d
              (FStar_Syntax_Syntax.Sig_datacon
                 (l, [], t1, FStar_Syntax_Const.exn_lid,
                   (Prims.parse_int "0"),
                   [FStar_Syntax_Syntax.ExceptionConstructor],
                   [FStar_Syntax_Const.exn_lid])) in
          let se' =
            sigelt_of_decl d
              (FStar_Syntax_Syntax.Sig_bundle
                 ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l])) in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
          let data_ops = mk_data_projector_names [] env1 ([], se) in
          let discs =
            mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l] in
          let env2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
              (FStar_List.append discs data_ops) in
          (env2, (FStar_List.append (se' :: discs) data_ops))
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
            let uu____10098 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10098 with
            | None  ->
                let uu____10100 =
                  let uu____10101 =
                    let uu____10104 =
                      let uu____10105 =
                        let uu____10106 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10106 " not found" in
                      Prims.strcat "Effect name " uu____10105 in
                    (uu____10104, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10101 in
                Prims.raise uu____10100
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10110 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10132 =
                  let uu____10137 =
                    let uu____10141 = desugar_term env t in ([], uu____10141) in
                  Some uu____10137 in
                (uu____10132, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10159 =
                  let uu____10164 =
                    let uu____10168 = desugar_term env wp in
                    ([], uu____10168) in
                  Some uu____10164 in
                let uu____10173 =
                  let uu____10178 =
                    let uu____10182 = desugar_term env t in ([], uu____10182) in
                  Some uu____10178 in
                (uu____10159, uu____10173)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10196 =
                  let uu____10201 =
                    let uu____10205 = desugar_term env t in ([], uu____10205) in
                  Some uu____10201 in
                (None, uu____10196) in
          (match uu____10110 with
           | (lift_wp,lift) ->
               let se =
                 sigelt_of_decl d
                   (FStar_Syntax_Syntax.Sig_sub_effect
                      {
                        FStar_Syntax_Syntax.source = src;
                        FStar_Syntax_Syntax.target = dst;
                        FStar_Syntax_Syntax.lift_wp = lift_wp;
                        FStar_Syntax_Syntax.lift = lift
                      }) in
               (env, [se]))
let desugar_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10256  ->
           fun d  ->
             match uu____10256 with
             | (env1,sigelts) ->
                 let uu____10268 = desugar_decl env1 d in
                 (match uu____10268 with
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
          | (None ,uu____10310) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10313;
               FStar_Syntax_Syntax.exports = uu____10314;
               FStar_Syntax_Syntax.is_interface = uu____10315;_},FStar_Parser_AST.Module
             (current_lid,uu____10317)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10322) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____10324 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10344 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____10344, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10354 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____10354, mname, decls, false) in
        match uu____10324 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10372 = desugar_decls env2 decls in
            (match uu____10372 with
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
          let uu____10397 =
            (FStar_Options.interactive ()) &&
              (let uu____10398 =
                 let uu____10399 =
                   let uu____10400 = FStar_Options.file_list () in
                   FStar_List.hd uu____10400 in
                 FStar_Util.get_file_extension uu____10399 in
               uu____10398 = "fsti") in
          if uu____10397
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10408,uu____10409) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m in
        let uu____10413 = desugar_modul_common curmod env m1 in
        match uu____10413 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10423 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10435 = desugar_modul_common None env m in
      match uu____10435 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____10446 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____10446
            then
              let uu____10447 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____10447
            else ());
           (let uu____10449 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____10449, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10460 =
        FStar_List.fold_left
          (fun uu____10467  ->
             fun m  ->
               match uu____10467 with
               | (env1,mods) ->
                   let uu____10479 = desugar_modul env1 m in
                   (match uu____10479 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____10460 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10503 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____10503 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___224_10509 = en1 in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___224_10509.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___224_10509.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___224_10509.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___224_10509.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___224_10509.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___224_10509.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___224_10509.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___224_10509.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___224_10509.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___224_10509.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___224_10509.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env