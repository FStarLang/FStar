open Prims
let trans_aqual :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___182_5  ->
    match uu___182_5 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____8 -> None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident Prims.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___183_19  ->
        match uu___183_19 with
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___184_25  ->
    match uu___184_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___185_32  ->
    match uu___185_32 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____34 -> None
  
let arg_withimp_e imp t = (t, (as_imp imp)) 
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____67 -> (t, None) 
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____76 -> true
            | uu____79 -> false))
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____84 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____88 =
      let uu____89 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____89  in
    FStar_Parser_AST.mk_term uu____88 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____93 =
      let uu____94 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____94  in
    FStar_Parser_AST.mk_term uu____93 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let uu____106 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____106 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____110,uu____111) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1
        |FStar_Parser_AST.Ascribed (t1,_)|FStar_Parser_AST.LetOpen (_,t1) ->
          is_comp_type env t1
      | uu____115 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____125 =
          let uu____127 =
            let uu____128 =
              let uu____131 = FStar_Parser_AST.compile_op n1 s  in
              (uu____131, r)  in
            FStar_Ident.mk_ident uu____128  in
          [uu____127]  in
        FStar_All.pipe_right uu____125 FStar_Ident.lid_of_ids
  
let op_as_term :
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
            let uu____155 =
              let uu____156 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None
                 in
              FStar_All.pipe_right uu____156 FStar_Syntax_Syntax.fv_to_tm  in
            Some uu____155  in
          let fallback uu____161 =
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
                let uu____163 = FStar_Options.ml_ish ()  in
                if uu____163
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
            | uu____166 -> None  in
          let uu____167 =
            let uu____171 = compile_op_lid arity s rng  in
            FStar_ToSyntax_Env.try_lookup_lid env uu____171  in
          match uu____167 with
          | Some t -> Some (Prims.fst t)
          | uu____178 -> fallback ()
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____188 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____188
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____213 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____216 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____216 with | (env1,uu____223) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____225,term) ->
          let uu____227 = free_type_vars env term  in (env, uu____227)
      | FStar_Parser_AST.TAnnotated (id,uu____231) ->
          let uu____232 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____232 with | (env1,uu____239) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____242 = free_type_vars env t  in (env, uu____242)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____247 =
        let uu____248 = unparen t  in uu____248.FStar_Parser_AST.tm  in
      match uu____247 with
      | FStar_Parser_AST.Labeled uu____250 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____256 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____256 with | None  -> [a] | uu____263 -> [])
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
          |FStar_Parser_AST.NamedTyp (_,t1)
           |FStar_Parser_AST.Paren t1|FStar_Parser_AST.Ascribed (t1,_)
          -> free_type_vars env t1
      | FStar_Parser_AST.Construct (uu____281,ts) ->
          FStar_List.collect
            (fun uu____291  ->
               match uu____291 with | (t1,uu____296) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____297,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____303) ->
          let uu____304 = free_type_vars env t1  in
          let uu____306 = free_type_vars env t2  in
          FStar_List.append uu____304 uu____306
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____310 = free_type_vars_b env b  in
          (match uu____310 with
           | (env1,f) ->
               let uu____319 = free_type_vars env1 t1  in
               FStar_List.append f uu____319)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____327 =
            FStar_List.fold_left
              (fun uu____334  ->
                 fun binder  ->
                   match uu____334 with
                   | (env1,free) ->
                       let uu____346 = free_type_vars_b env1 binder  in
                       (match uu____346 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____327 with
           | (env1,free) ->
               let uu____364 = free_type_vars env1 body  in
               FStar_List.append free uu____364)
      | FStar_Parser_AST.Project (t1,uu____367) -> free_type_vars env t1
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

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____406 =
        let uu____407 = unparen t1  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____431 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____445 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____445  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____457 =
                     let uu____458 =
                       let uu____461 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____461)  in
                     FStar_Parser_AST.TAnnotated uu____458  in
                   FStar_Parser_AST.mk_binder uu____457 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
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
        let uu____472 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____472  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____484 =
                     let uu____485 =
                       let uu____488 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____488)  in
                     FStar_Parser_AST.TAnnotated uu____485  in
                   FStar_Parser_AST.mk_binder uu____484 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____490 =
             let uu____491 = unparen t  in uu____491.FStar_Parser_AST.tm  in
           match uu____490 with
           | FStar_Parser_AST.Product uu____492 -> t
           | uu____496 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Syntax_Const.effect_Tot_lid)
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
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____517 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____529) -> is_var_pattern p1
    | uu____530 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____535) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____536;
           FStar_Parser_AST.prange = uu____537;_},uu____538)
        -> true
    | uu____544 -> false
  
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
    | uu____548 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term
          Prims.option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____574 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____574 with
             | (name,args,uu____591) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____605);
               FStar_Parser_AST.prange = uu____606;_},args)
            when is_top_level1 ->
            let uu____612 =
              let uu____615 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____615  in
            (uu____612, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____621);
               FStar_Parser_AST.prange = uu____622;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____632 -> failwith "Not an app pattern"
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild 
        |FStar_Parser_AST.PatConst _
         |FStar_Parser_AST.PatVar (_,Some (FStar_Parser_AST.Implicit ))
          |FStar_Parser_AST.PatName _
           |FStar_Parser_AST.PatTvar _|FStar_Parser_AST.PatOp _
          -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____667) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____680 = FStar_List.map Prims.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____680
      | FStar_Parser_AST.PatAscribed (pat,uu____685) ->
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
      (fun uu____694  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____712 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____732 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___186_750  ->
    match uu___186_750 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____755 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___187_772  ->
        match uu___187_772 with
        | (None ,k) ->
            let uu____781 = FStar_Syntax_Syntax.null_binder k  in
            (uu____781, env)
        | (Some a,k) ->
            let uu____785 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____785 with
             | (env1,a1) ->
                 (((let uu___208_796 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___208_796.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___208_796.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb :
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____809  ->
    match uu____809 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
  
let no_annot_abs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None 
let mk_ref_read tm =
  let tm' =
    let uu____865 =
      let uu____875 =
        let uu____876 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____876  in
      let uu____877 =
        let uu____883 =
          let uu____888 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____888)  in
        [uu____883]  in
      (uu____875, uu____877)  in
    FStar_Syntax_Syntax.Tm_app uu____865  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____922 =
      let uu____932 =
        let uu____933 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____933  in
      let uu____934 =
        let uu____940 =
          let uu____945 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____945)  in
        [uu____940]  in
      (uu____932, uu____934)  in
    FStar_Syntax_Syntax.Tm_app uu____922  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____993 =
      let uu____1003 =
        let uu____1004 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1004  in
      let uu____1005 =
        let uu____1011 =
          let uu____1016 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1016)  in
        let uu____1019 =
          let uu____1025 =
            let uu____1030 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1030)  in
          [uu____1025]  in
        uu____1011 :: uu____1019  in
      (uu____1003, uu____1005)  in
    FStar_Syntax_Syntax.Tm_app uu____993  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___188_1056  ->
    match uu___188_1056 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1057 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1065 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1065)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1076 =
      let uu____1077 = unparen t  in uu____1077.FStar_Parser_AST.tm  in
    match uu____1076 with
    | FStar_Parser_AST.Wild  ->
        let uu____1080 =
          let uu____1081 = FStar_Unionfind.fresh None  in
          FStar_Syntax_Syntax.U_unif uu____1081  in
        FStar_Util.Inr uu____1080
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1087)) ->
        let n1 = FStar_Util.int_of_string repr  in
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
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u)
           |(FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1130 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1130
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1137 =
               let uu____1138 =
                 let uu____1141 =
                   let uu____1142 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1142
                    in
                 (uu____1141, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1138  in
             Prims.raise uu____1137)
    | FStar_Parser_AST.App uu____1145 ->
        let rec aux t1 univargs =
          let uu____1164 =
            let uu____1165 = unparen t1  in uu____1165.FStar_Parser_AST.tm
             in
          match uu____1164 with
          | FStar_Parser_AST.App (t2,targ,uu____1170) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___189_1182  ->
                     match uu___189_1182 with
                     | FStar_Util.Inr uu____1185 -> true
                     | uu____1186 -> false) univargs
              then
                let uu____1189 =
                  let uu____1190 =
                    FStar_List.map
                      (fun uu___190_1194  ->
                         match uu___190_1194 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1190  in
                FStar_Util.Inr uu____1189
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___191_1204  ->
                        match uu___191_1204 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1208 -> failwith "impossible")
                     univargs
                    in
                 let uu____1209 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1209)
          | uu____1213 ->
              let uu____1214 =
                let uu____1215 =
                  let uu____1218 =
                    let uu____1219 =
                      let uu____1220 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1220 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1219  in
                  (uu____1218, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1215  in
              Prims.raise uu____1214
           in
        aux t []
    | uu____1225 ->
        let uu____1226 =
          let uu____1227 =
            let uu____1230 =
              let uu____1231 =
                let uu____1232 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1232 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1231  in
            (uu____1230, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1227  in
        Prims.raise uu____1226
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1266 = FStar_List.hd fields  in
  match uu____1266 with
  | (f,uu____1272) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
         in
      let check_field uu____1279 =
        match uu____1279 with
        | (f',uu____1283) ->
            let uu____1284 =
              FStar_ToSyntax_Env.belongs_to_record env f' record  in
            if uu____1284
            then ()
            else
              (let msg =
                 FStar_Util.format3
                   "Field %s belongs to record type %s, whereas field %s does not"
                   f.FStar_Ident.str
                   (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                   f'.FStar_Ident.str
                  in
               Prims.raise (FStar_Errors.Error (msg, rg)))
         in
      ((let uu____1288 = FStar_List.tl fields  in
        FStar_List.iter check_field uu____1288);
       (match () with | () -> record))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat)
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1444,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1466  ->
                          match uu____1466 with
                          | (p3,uu____1472) ->
                              let uu____1473 = pat_vars p3  in
                              FStar_Util.set_union out uu____1473)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1  in
                let uu____1487 =
                  let uu____1488 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3  in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1
                     in
                  Prims.op_Negation uu____1488  in
                if uu____1487
                then
                  Prims.raise
                    (FStar_Errors.Error
                       ("Disjunctive pattern binds different variables in each case",
                         (p2.FStar_Syntax_Syntax.p)))
                else xs
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1495) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1523 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1523 with
           | Some y -> (l, e, y)
           | uu____1531 ->
               let uu____1533 = push_bv_maybe_mut e x  in
               (match uu____1533 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange
              in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
              in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOp op ->
               let uu____1582 =
                 let uu____1583 =
                   let uu____1584 =
                     let uu____1588 =
                       let uu____1589 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op
                          in
                       FStar_Ident.id_of_text uu____1589  in
                     (uu____1588, None)  in
                   FStar_Parser_AST.PatVar uu____1584  in
                 {
                   FStar_Parser_AST.pat = uu____1583;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1582
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1601 = aux loc env1 p2  in
               (match uu____1601 with
                | (loc1,env2,var,p3,uu____1620) ->
                    let uu____1625 =
                      FStar_List.fold_left
                        (fun uu____1638  ->
                           fun p4  ->
                             match uu____1638 with
                             | (loc2,env3,ps1) ->
                                 let uu____1661 = aux loc2 env3 p4  in
                                 (match uu____1661 with
                                  | (loc3,env4,uu____1677,p5,uu____1679) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____1625 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1)))
                            in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1723 = aux loc env1 p2  in
               (match uu____1723 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1748 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1754 = close_fun env1 t  in
                            desugar_term env1 uu____1754  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1756 -> true)
                           then
                             (let uu____1757 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1758 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1759 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1757 uu____1758 uu____1759)
                           else ();
                           LocalBinder
                             (((let uu___209_1761 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_1761.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_1761.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq))
                       in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1765 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1765, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1775 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1775, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1793 = resolvex loc env1 x  in
               (match uu____1793 with
                | (loc1,env2,xbv) ->
                    let uu____1807 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1807, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1818 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1818, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1836;_},args)
               ->
               let uu____1840 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1858  ->
                        match uu____1858 with
                        | (loc1,env2,args1) ->
                            let uu____1888 = aux loc1 env2 arg  in
                            (match uu____1888 with
                             | (loc2,env3,uu____1906,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1840 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____1955 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____1955, false))
           | FStar_Parser_AST.PatApp uu____1968 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1981 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____1995  ->
                        match uu____1995 with
                        | (loc1,env2,pats1) ->
                            let uu____2017 = aux loc1 env2 pat  in
                            (match uu____2017 with
                             | (loc2,env3,uu____2033,pat1,uu____2035) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____1981 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2069 =
                        let uu____2072 =
                          let uu____2077 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2077  in
                        let uu____2078 =
                          let uu____2079 =
                            let uu____2087 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2087, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2079  in
                        FStar_All.pipe_left uu____2072 uu____2078  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2110 =
                               let uu____2111 =
                                 let uu____2119 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2119, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2111  in
                             FStar_All.pipe_left (pos_r r) uu____2110) pats1
                        uu____2069
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2151 =
                 FStar_List.fold_left
                   (fun uu____2168  ->
                      fun p2  ->
                        match uu____2168 with
                        | (loc1,env2,pats) ->
                            let uu____2199 = aux loc1 env2 p2  in
                            (match uu____2199 with
                             | (loc2,env3,uu____2217,pat,uu____2219) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2151 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Syntax_Util.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Syntax_Util.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____2290 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2290 with
                     | (constr,uu____2303) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2306 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2308 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2308,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2349  ->
                         match uu____2349 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2364  ->
                         match uu____2364 with
                         | (f,uu____2368) ->
                             let uu____2369 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2381  ->
                                       match uu____2381 with
                                       | (g,uu____2385) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2369 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2388,p2) -> p2)))
                  in
               let app =
                 let uu____2393 =
                   let uu____2394 =
                     let uu____2398 =
                       let uu____2399 =
                         let uu____2400 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2400  in
                       FStar_Parser_AST.mk_pattern uu____2399
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2398, args)  in
                   FStar_Parser_AST.PatApp uu____2394  in
                 FStar_Parser_AST.mk_pattern uu____2393
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2402 = aux loc env1 app  in
               (match uu____2402 with
                | (env2,e,b,p2,uu____2421) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2443 =
                            let uu____2444 =
                              let uu____2452 =
                                let uu___210_2453 = fv  in
                                let uu____2454 =
                                  let uu____2456 =
                                    let uu____2457 =
                                      let uu____2461 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2461)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2457
                                     in
                                  Some uu____2456  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___210_2453.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___210_2453.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2454
                                }  in
                              (uu____2452, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2444  in
                          FStar_All.pipe_left pos uu____2443
                      | uu____2480 -> p2  in
                    (env2, e, b, p3, false))
            in
         let uu____2483 = aux [] env p  in
         match uu____2483 with
         | (uu____2494,env1,b,p1,uu____2498) ->
             ((let uu____2504 = check_linear_pattern_variables p1  in
               FStar_All.pipe_left Prims.ignore uu____2504);
              (env1, b, p1)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2523 =
              let uu____2524 =
                let uu____2527 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2527, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2524  in
            (env, uu____2523, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2538 =
                  let uu____2539 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x  in
                  FStar_Ident.id_of_text uu____2539  in
                mklet uu____2538
            | FStar_Parser_AST.PatVar (x,uu____2541) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2545);
                   FStar_Parser_AST.prange = uu____2546;_},t)
                ->
                let uu____2550 =
                  let uu____2551 =
                    let uu____2554 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2555 = desugar_term env t  in
                    (uu____2554, uu____2555)  in
                  LetBinder uu____2551  in
                (env, uu____2550, None)
            | uu____2557 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2563 = desugar_data_pat env p is_mut  in
             match uu____2563 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2579 -> Some p1  in
                 (env1, binder, p2))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  =
  fun uu____2583  ->
    fun env  ->
      fun pat  ->
        let uu____2586 = desugar_data_pat env pat false  in
        match uu____2586 with | (env1,uu____2593,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___211_2600 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2600.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2600.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2600.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2600.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2600.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2600.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2600.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2600.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2600.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2600.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2600.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        }  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___212_2604 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___212_2604.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___212_2604.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___212_2604.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___212_2604.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___212_2604.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___212_2604.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___212_2604.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___212_2604.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___212_2604.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___212_2604.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___212_2604.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true
        }  in
      desugar_term_maybe_top false env1 e

and desugar_machine_integer :
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2607  ->
        fun range  ->
          match uu____2607 with
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
                                  | FStar_Const.Signed  -> "") "int_to_t")))))
                 in
              let lid1 =
                FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range
                 in
              let lid2 =
                let uu____2618 = FStar_ToSyntax_Env.try_lookup_lid env lid1
                   in
                match uu____2618 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2629 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1)
                       in
                    failwith uu____2629
                 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              let uu____2646 =
                let uu____2649 =
                  let uu____2650 =
                    let uu____2660 =
                      let uu____2666 =
                        let uu____2671 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____2671)  in
                      [uu____2666]  in
                    (lid2, uu____2660)  in
                  FStar_Syntax_Syntax.Tm_app uu____2650  in
                FStar_Syntax_Syntax.mk uu____2649  in
              uu____2646 None range

and desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun l  ->
          let uu____2705 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env) l
             in
          match uu____2705 with
          | (tm,mut) ->
              let tm1 = setpos tm  in
              if mut
              then
                let uu____2715 =
                  let uu____2716 =
                    let uu____2721 = mk_ref_read tm1  in
                    (uu____2721,
                      (FStar_Syntax_Syntax.Meta_desugared
                         FStar_Syntax_Syntax.Mutable_rval))
                     in
                  FStar_Syntax_Syntax.Tm_meta uu____2716  in
                FStar_All.pipe_left mk1 uu____2715
              else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2735 =
          let uu____2736 = unparen t  in uu____2736.FStar_Parser_AST.tm  in
        match uu____2735 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2737; FStar_Ident.ident = uu____2738;
              FStar_Ident.nsstr = uu____2739; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2741 ->
            let uu____2742 =
              let uu____2743 =
                let uu____2746 =
                  let uu____2747 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____2747  in
                (uu____2746, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____2743  in
            Prims.raise uu____2742
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range  in
        let setpos e =
          let uu___213_2775 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___213_2775.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___213_2775.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___213_2775.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2782 =
          let uu____2783 = unparen top  in uu____2783.FStar_Parser_AST.tm  in
        match uu____2782 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2784 -> desugar_formula env top
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
        | FStar_Parser_AST.Op ("*",uu____2813::uu____2814::[]) when
            let uu____2816 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*"
               in
            FStar_All.pipe_right uu____2816 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2828 = flatten1 t1  in
                  FStar_List.append uu____2828 [t2]
              | uu____2830 -> [t]  in
            let targs =
              let uu____2833 =
                let uu____2835 = unparen top  in flatten1 uu____2835  in
              FStar_All.pipe_right uu____2833
                (FStar_List.map
                   (fun t  ->
                      let uu____2839 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____2839))
               in
            let uu____2840 =
              let uu____2843 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2843
               in
            (match uu____2840 with
             | (tup,uu____2850) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2853 =
              let uu____2856 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              Prims.fst uu____2856  in
            FStar_All.pipe_left setpos uu____2853
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2870 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2870 with
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
                             let uu____2892 = desugar_term env t  in
                             (uu____2892, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2899; FStar_Ident.ident = uu____2900;
              FStar_Ident.nsstr = uu____2901; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2903; FStar_Ident.ident = uu____2904;
              FStar_Ident.nsstr = uu____2905; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2907; FStar_Ident.ident = uu____2908;
               FStar_Ident.nsstr = uu____2909; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2919 =
              let uu____2920 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____2920  in
            mk1 uu____2919
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2921; FStar_Ident.ident = uu____2922;
              FStar_Ident.nsstr = uu____2923; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2925; FStar_Ident.ident = uu____2926;
              FStar_Ident.nsstr = uu____2927; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2929; FStar_Ident.ident = uu____2930;
              FStar_Ident.nsstr = uu____2931; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2935;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2936 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
            (match uu____2936 with
             | Some ed ->
                 let uu____2939 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2939
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  -> failwith "immpossible special_effect_combinator")
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____2943 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2943 with
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
            desugar_name mk1 setpos env l
        | FStar_Parser_AST.Projector (l,i) ->
            let found =
              (let uu____2956 = FStar_ToSyntax_Env.try_lookup_datacon env l
                  in
               FStar_Option.isSome uu____2956) ||
                (let uu____2958 =
                   FStar_ToSyntax_Env.try_lookup_effect_defn env l  in
                 FStar_Option.isSome uu____2958)
               in
            if found
            then
              let uu____2960 =
                FStar_Syntax_Util.mk_field_projector_name_from_ident l i  in
              desugar_name mk1 setpos env uu____2960
            else
              (let uu____2962 =
                 let uu____2963 =
                   let uu____2966 =
                     FStar_Util.format1
                       "Data constructor or effect %s not found"
                       l.FStar_Ident.str
                      in
                   (uu____2966, (top.FStar_Parser_AST.range))  in
                 FStar_Errors.Error uu____2963  in
               Prims.raise uu____2962)
        | FStar_Parser_AST.Discrim lid ->
            let uu____2968 = FStar_ToSyntax_Env.try_lookup_datacon env lid
               in
            (match uu____2968 with
             | None  ->
                 let uu____2970 =
                   let uu____2971 =
                     let uu____2974 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str
                        in
                     (uu____2974, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____2971  in
                 Prims.raise uu____2970
             | uu____2975 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 desugar_name mk1 setpos env lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____2986 = FStar_ToSyntax_Env.try_lookup_datacon env l  in
            (match uu____2986 with
             | Some head1 ->
                 let uu____2989 =
                   let uu____2994 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                      in
                   (uu____2994, true)  in
                 (match uu____2989 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3007 ->
                           let uu____3011 =
                             FStar_Util.take
                               (fun uu____3022  ->
                                  match uu____3022 with
                                  | (uu____3025,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args
                              in
                           (match uu____3011 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes
                                   in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3058  ->
                                       match uu____3058 with
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
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")),
                        (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3093 =
              FStar_List.fold_left
                (fun uu____3110  ->
                   fun b  ->
                     match uu____3110 with
                     | (env1,tparams,typs) ->
                         let uu____3141 = desugar_binder env1 b  in
                         (match uu____3141 with
                          | (xopt,t1) ->
                              let uu____3157 =
                                match xopt with
                                | None  ->
                                    let uu____3162 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3162)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3157 with
                               | (env2,x) ->
                                   let uu____3174 =
                                     let uu____3176 =
                                       let uu____3178 =
                                         let uu____3179 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3179
                                          in
                                       [uu____3178]  in
                                     FStar_List.append typs uu____3176  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___214_3192 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___214_3192.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___214_3192.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3174))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3093 with
             | (env1,uu____3205,targs) ->
                 let uu____3217 =
                   let uu____3220 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3220
                    in
                 (match uu____3217 with
                  | (tup,uu____3227) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3235 = uncurry binders t  in
            (match uu____3235 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___192_3258 =
                   match uu___192_3258 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3266 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3266
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3282 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3282 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3293 = desugar_binder env b  in
            (match uu____3293 with
             | (None ,uu____3297) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3303 = as_binder env None b1  in
                 (match uu____3303 with
                  | ((x,uu____3307),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3312 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3312))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3327 =
              FStar_List.fold_left
                (fun uu____3334  ->
                   fun pat  ->
                     match uu____3334 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3349,t) ->
                              let uu____3351 =
                                let uu____3353 = free_type_vars env1 t  in
                                FStar_List.append uu____3353 ftvs  in
                              (env1, uu____3351)
                          | uu____3356 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3327 with
             | (uu____3359,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3367 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3367 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___193_3396 =
                   match uu___193_3396 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3425 =
                                 let uu____3426 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3426
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3425 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3468 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3468
                   | p::rest ->
                       let uu____3476 = desugar_binding_pat env1 p  in
                       (match uu____3476 with
                        | (env2,b,pat) ->
                            let uu____3488 =
                              match b with
                              | LetBinder uu____3507 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3538) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3561 =
                                          let uu____3564 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____3564, p1)  in
                                        Some uu____3561
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3589,uu____3590) ->
                                             let tup2 =
                                               let uu____3592 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3592
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3596 =
                                                 let uu____3599 =
                                                   let uu____3600 =
                                                     let uu____3610 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____3613 =
                                                       let uu____3615 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____3616 =
                                                         let uu____3618 =
                                                           let uu____3619 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3619
                                                            in
                                                         [uu____3618]  in
                                                       uu____3615 ::
                                                         uu____3616
                                                        in
                                                     (uu____3610, uu____3613)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3600
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3599
                                                  in
                                               uu____3596 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____3634 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3634
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3654,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3656,pats)) ->
                                             let tupn =
                                               let uu____3683 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3683
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3693 =
                                                 let uu____3694 =
                                                   let uu____3704 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____3707 =
                                                     let uu____3713 =
                                                       let uu____3719 =
                                                         let uu____3720 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3720
                                                          in
                                                       [uu____3719]  in
                                                     FStar_List.append args
                                                       uu____3713
                                                      in
                                                   (uu____3704, uu____3707)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3694
                                                  in
                                               mk1 uu____3693  in
                                             let p2 =
                                               let uu____3735 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3735
                                                in
                                             Some (sc1, p2)
                                         | uu____3759 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3488 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var a;
               FStar_Parser_AST.range = rng;
               FStar_Parser_AST.level = uu____3802;_},phi,uu____3804)
            when
            (FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
              (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)
            ->
            let phi1 = desugar_formula env phi  in
            let a1 = FStar_Ident.set_lid_range a rng  in
            let uu____3807 =
              let uu____3808 =
                let uu____3818 =
                  FStar_Syntax_Syntax.fvar a1
                    FStar_Syntax_Syntax.Delta_equational None
                   in
                let uu____3819 =
                  let uu____3821 = FStar_Syntax_Syntax.as_arg phi1  in
                  let uu____3822 =
                    let uu____3824 =
                      let uu____3825 =
                        mk1
                          (FStar_Syntax_Syntax.Tm_constant
                             FStar_Const.Const_unit)
                         in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3825
                       in
                    [uu____3824]  in
                  uu____3821 :: uu____3822  in
                (uu____3818, uu____3819)  in
              FStar_Syntax_Syntax.Tm_app uu____3808  in
            mk1 uu____3807
        | FStar_Parser_AST.App
            (uu____3827,uu____3828,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3840 =
                let uu____3841 = unparen e  in uu____3841.FStar_Parser_AST.tm
                 in
              match uu____3840 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____3847 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3850 ->
            let rec aux args e =
              let uu____3871 =
                let uu____3872 = unparen e  in uu____3872.FStar_Parser_AST.tm
                 in
              match uu____3871 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3882 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3882  in
                  aux (arg :: args) e1
              | uu____3889 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3900 =
              let uu____3901 =
                let uu____3906 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____3906,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3901  in
            mk1 uu____3900
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3936 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____3978  ->
                        match uu____3978 with
                        | (p,def) ->
                            let uu____3992 = is_app_pattern p  in
                            if uu____3992
                            then
                              let uu____4002 =
                                destruct_app_pattern env top_level p  in
                              (uu____4002, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4031 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4031, def1)
                               | uu____4046 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4060);
                                           FStar_Parser_AST.prange =
                                             uu____4061;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4074 =
                                            let uu____4082 =
                                              let uu____4085 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4085  in
                                            (uu____4082, [], (Some t))  in
                                          (uu____4074, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4110)
                                        ->
                                        if top_level
                                        then
                                          let uu____4122 =
                                            let uu____4130 =
                                              let uu____4133 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4133  in
                                            (uu____4130, [], None)  in
                                          (uu____4122, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4157 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4167 =
                FStar_List.fold_left
                  (fun uu____4191  ->
                     fun uu____4192  ->
                       match (uu____4191, uu____4192) with
                       | ((env1,fnames,rec_bindings),((f,uu____4236,uu____4237),uu____4238))
                           ->
                           let uu____4278 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4292 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4292 with
                                  | (env2,xx) ->
                                      let uu____4303 =
                                        let uu____4305 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4305 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4303))
                             | FStar_Util.Inr l ->
                                 let uu____4310 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4310, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4278 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4167 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4383 =
                    match uu____4383 with
                    | ((uu____4395,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4421 = is_comp_type env1 t  in
                                if uu____4421
                                then
                                  ((let uu____4423 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4428 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4428))
                                       in
                                    match uu____4423 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4431 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4432 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4432))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4431
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4437 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1))
                                uu____4437 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4439 ->
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
                              let uu____4449 =
                                let uu____4450 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4450
                                  None
                                 in
                              FStar_Util.Inr uu____4449
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        mk_lb (lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____4470 =
                    let uu____4471 =
                      let uu____4479 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4479)  in
                    FStar_Syntax_Syntax.Tm_let uu____4471  in
                  FStar_All.pipe_left mk1 uu____4470
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4506 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4506 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4527 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4527 None  in
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
                    | LocalBinder (x,uu____4535) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat2 with
                          | None |Some
                            {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild _;
                              FStar_Syntax_Syntax.ty = _;
                              FStar_Syntax_Syntax.p = _;_} -> body1
                          | Some pat3 ->
                              let uu____4544 =
                                let uu____4547 =
                                  let uu____4548 =
                                    let uu____4564 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____4565 =
                                      let uu____4567 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1)
                                         in
                                      [uu____4567]  in
                                    (uu____4564, uu____4565)  in
                                  FStar_Syntax_Syntax.Tm_match uu____4548  in
                                FStar_Syntax_Syntax.mk uu____4547  in
                              uu____4544 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____4582 =
                          let uu____4583 =
                            let uu____4591 =
                              let uu____4592 =
                                let uu____4593 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____4593]  in
                              FStar_Syntax_Subst.close uu____4592 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4591)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____4583  in
                        FStar_All.pipe_left mk1 uu____4582
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
            let uu____4613 = is_rec || (is_app_pattern pat)  in
            if uu____4613
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____4619 =
              let uu____4620 =
                let uu____4636 = desugar_term env t1  in
                let uu____4637 =
                  let uu____4647 =
                    let uu____4656 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____4659 = desugar_term env t2  in
                    (uu____4656, None, uu____4659)  in
                  let uu____4667 =
                    let uu____4677 =
                      let uu____4686 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____4689 = desugar_term env t3  in
                      (uu____4686, None, uu____4689)  in
                    [uu____4677]  in
                  uu____4647 :: uu____4667  in
                (uu____4636, uu____4637)  in
              FStar_Syntax_Syntax.Tm_match uu____4620  in
            mk1 uu____4619
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Syntax_Const.try_with_lid)
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
            let desugar_branch uu____4775 =
              match uu____4775 with
              | (pat,wopt,b) ->
                  let uu____4785 = desugar_match_pat env pat  in
                  (match uu____4785 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4794 = desugar_term env1 e1  in
                             Some uu____4794
                          in
                       let b1 = desugar_term env1 b  in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1))
               in
            let uu____4797 =
              let uu____4798 =
                let uu____4814 = desugar_term env e  in
                let uu____4815 = FStar_List.map desugar_branch branches  in
                (uu____4814, uu____4815)  in
              FStar_Syntax_Syntax.Tm_match uu____4798  in
            FStar_All.pipe_left mk1 uu____4797
        | FStar_Parser_AST.Ascribed (e,t) ->
            let annot =
              let uu____4829 = is_comp_type env t  in
              if uu____4829
              then
                let uu____4832 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____4832
              else
                (let uu____4834 = desugar_term env t  in
                 FStar_Util.Inl uu____4834)
               in
            let uu____4835 =
              let uu____4836 =
                let uu____4849 = desugar_term env e  in
                (uu____4849, annot, None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____4836  in
            FStar_All.pipe_left mk1 uu____4835
        | FStar_Parser_AST.Record (uu____4855,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____4876 = FStar_List.hd fields  in
              match uu____4876 with | (f,uu____4883) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4907  ->
                        match uu____4907 with
                        | (g,uu____4911) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____4915,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4923 =
                         let uu____4924 =
                           let uu____4927 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____4927, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____4924  in
                       Prims.raise uu____4923
                   | Some x ->
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
              | None  ->
                  let uu____4933 =
                    let uu____4939 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____4953  ->
                              match uu____4953 with
                              | (f,uu____4959) ->
                                  let uu____4960 =
                                    let uu____4961 = get_field None f  in
                                    FStar_All.pipe_left Prims.snd uu____4961
                                     in
                                  (uu____4960, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____4939)  in
                  FStar_Parser_AST.Construct uu____4933
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____4972 =
                      let uu____4973 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____4973  in
                    FStar_Parser_AST.mk_term uu____4972 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____4975 =
                      let uu____4982 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____4996  ->
                                match uu____4996 with
                                | (f,uu____5002) -> get_field (Some xterm) f))
                         in
                      (None, uu____4982)  in
                    FStar_Parser_AST.Record uu____4975  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
                           x.FStar_Ident.idRange), e)],
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
                         FStar_Syntax_Syntax.tk = uu____5018;
                         FStar_Syntax_Syntax.pos = uu____5019;
                         FStar_Syntax_Syntax.vars = uu____5020;_},args);
                    FStar_Syntax_Syntax.tk = uu____5022;
                    FStar_Syntax_Syntax.pos = uu____5023;
                    FStar_Syntax_Syntax.vars = uu____5024;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5046 =
                     let uu____5047 =
                       let uu____5057 =
                         let uu____5058 =
                           let uu____5060 =
                             let uu____5061 =
                               let uu____5065 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5065)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5061  in
                           Some uu____5060  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5058
                          in
                       (uu____5057, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5047  in
                   FStar_All.pipe_left mk1 uu____5046  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5089 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5092 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
               in
            (match uu____5092 with
             | (constrname,is_rec) ->
                 let e1 = desugar_term env e  in
                 let projname =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     constrname f.FStar_Ident.ident
                    in
                 let qual1 =
                   if is_rec
                   then
                     Some
                       (FStar_Syntax_Syntax.Record_projector
                          (constrname, (f.FStar_Ident.ident)))
                   else None  in
                 let uu____5105 =
                   let uu____5106 =
                     let uu____5116 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual1
                        in
                     let uu____5117 =
                       let uu____5119 = FStar_Syntax_Syntax.as_arg e1  in
                       [uu____5119]  in
                     (uu____5116, uu____5117)  in
                   FStar_Syntax_Syntax.Tm_app uu____5106  in
                 FStar_All.pipe_left mk1 uu____5105)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5125 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5126 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5127,uu____5128,uu____5129) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5136,uu____5137,uu____5138) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5145,uu____5146,uu____5147) ->
            failwith "Not implemented yet"

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        Prims.option) Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5171  ->
              match uu____5171 with
              | (a,imp) ->
                  let uu____5179 = desugar_term env a  in
                  arg_withimp_e imp uu____5179))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term -> FStar_Syntax_Syntax.comp
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5196 =
          match uu____5196 with
          | (t1,uu____5200) ->
              let uu____5201 =
                let uu____5202 = unparen t1  in
                uu____5202.FStar_Parser_AST.tm  in
              (match uu____5201 with
               | FStar_Parser_AST.Requires uu____5203 -> true
               | uu____5207 -> false)
           in
        let is_ensures uu____5213 =
          match uu____5213 with
          | (t1,uu____5217) ->
              let uu____5218 =
                let uu____5219 = unparen t1  in
                uu____5219.FStar_Parser_AST.tm  in
              (match uu____5218 with
               | FStar_Parser_AST.Ensures uu____5220 -> true
               | uu____5224 -> false)
           in
        let is_app head1 uu____5233 =
          match uu____5233 with
          | (t1,uu____5237) ->
              let uu____5238 =
                let uu____5239 = unparen t1  in
                uu____5239.FStar_Parser_AST.tm  in
              (match uu____5238 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5241;
                      FStar_Parser_AST.level = uu____5242;_},uu____5243,uu____5244)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5245 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5263 = head_and_args t1  in
          match uu____5263 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
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
                       FStar_Parser_AST.Nothing)
                      in
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5428 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____5428, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5442 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5442
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5451 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5451
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
               | uu____5471 ->
                   let default_effect =
                     let uu____5473 = FStar_Options.ml_ish ()  in
                     if uu____5473
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5476 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____5476
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Syntax_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____5489 = pre_process_comp_typ t  in
        match uu____5489 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5517 =
                  let uu____5518 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5518
                   in
                fail uu____5517)
             else ();
             (let is_universe uu____5525 =
                match uu____5525 with
                | (uu____5528,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____5530 = FStar_Util.take is_universe args  in
              match uu____5530 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5559  ->
                         match uu____5559 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____5564 =
                    let uu____5572 = FStar_List.hd args1  in
                    let uu____5577 = FStar_List.tl args1  in
                    (uu____5572, uu____5577)  in
                  (match uu____5564 with
                   | (first_arg,rest) ->
                       let first_typ = desugar_typ env (Prims.fst first_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____5606 =
                         FStar_All.pipe_right rest1
                           (FStar_List.partition
                              (fun uu____5644  ->
                                 match uu____5644 with
                                 | (t1,uu____5651) ->
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____5659;
                                             FStar_Syntax_Syntax.pos =
                                               uu____5660;
                                             FStar_Syntax_Syntax.vars =
                                               uu____5661;_},uu____5662::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____5684 -> false)))
                          in
                       (match uu____5606 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5725  ->
                                      match uu____5725 with
                                      | (t1,uu____5732) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5739,(arg,uu____5741)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5763 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5775 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Syntax_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total first_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Syntax_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal first_typ
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
                                         else []
                                    in
                                 let flags1 =
                                   FStar_List.append flags cattributes  in
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
                                                      FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 let uu____5863 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____5863
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____5875 -> pat  in
                                         let uu____5876 =
                                           let uu____5883 =
                                             let uu____5890 =
                                               let uu____5896 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____5896, aq)  in
                                             [uu____5890]  in
                                           ens :: uu____5883  in
                                         req :: uu____5876
                                     | uu____5932 -> rest2
                                   else rest2  in
                                 let uu____5940 =
                                   let uu____5941 =
                                     let uu____5947 =
                                       FStar_Syntax_Syntax.as_arg first_typ
                                        in
                                     uu____5947 :: rest3  in
                                   {
                                     FStar_Syntax_Syntax.comp_typ_name = eff;
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____5941;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags1
                                          decreases_clause)
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____5940)))))

and desugar_formula :
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
        | uu____5956 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___215_5997 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___215_5997.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___215_5997.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___215_5997.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___216_6027 = b  in
             {
               FStar_Parser_AST.b = (uu___216_6027.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___216_6027.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___216_6027.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6060 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6060)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6069 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6069 with
             | (env1,a1) ->
                 let a2 =
                   let uu___217_6077 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___217_6077.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___217_6077.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6090 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6099 =
                     let uu____6102 =
                       let uu____6106 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6106]  in
                     no_annot_abs uu____6102 body2  in
                   FStar_All.pipe_left setpos uu____6099  in
                 let uu____6111 =
                   let uu____6112 =
                     let uu____6122 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6123 =
                       let uu____6125 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6125]  in
                     (uu____6122, uu____6123)  in
                   FStar_Syntax_Syntax.Tm_app uu____6112  in
                 FStar_All.pipe_left mk1 uu____6111)
        | uu____6129 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6178 = q (rest, pats, body)  in
              let uu____6182 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6178 uu____6182
                FStar_Parser_AST.Formula
               in
            let uu____6183 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6183 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6188 -> failwith "impossible"  in
      let uu____6190 =
        let uu____6191 = unparen f  in uu____6191.FStar_Parser_AST.tm  in
      match uu____6190 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],_,_)|FStar_Parser_AST.QExists ([],_,_)
          -> failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6221 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6221
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6242 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6242
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6267 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6271 =
        FStar_List.fold_left
          (fun uu____6284  ->
             fun b  ->
               match uu____6284 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___218_6312 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___218_6312.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___218_6312.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___218_6312.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6322 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6322 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___219_6334 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___219_6334.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___219_6334.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6343 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6271 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6393 = desugar_typ env t  in ((Some x), uu____6393)
      | FStar_Parser_AST.TVariable x ->
          let uu____6396 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____6396)
      | FStar_Parser_AST.NoName t ->
          let uu____6411 = desugar_typ env t  in (None, uu____6411)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___194_6460  ->
            match uu___194_6460 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6461 -> false))
     in
  let quals2 q =
    let uu____6469 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface
       in
    if uu____6469
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          let uu____6476 =
            let uu____6483 =
              quals2
                [FStar_Syntax_Syntax.OnlyName;
                FStar_Syntax_Syntax.Discriminator d]
               in
            (disc_name, [], FStar_Syntax_Syntax.tun, uu____6483,
              (FStar_Ident.range_of_lid disc_name))
             in
          FStar_Syntax_Syntax.Sig_declare_typ uu____6476))
  
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
            let uu____6508 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6518  ->
                        match uu____6518 with
                        | (x,uu____6523) ->
                            let uu____6524 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____6524 with
                             | (field_name,uu____6529) ->
                                 let only_decl =
                                   ((let uu____6531 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6531)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6532 =
                                        let uu____6533 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____6533.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____6532)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6543 =
                                       FStar_List.filter
                                         (fun uu___195_6545  ->
                                            match uu___195_6545 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6546 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6543
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___196_6554  ->
                                             match uu___196_6554 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6555 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun, quals1,
                                       (FStar_Ident.range_of_lid field_name))
                                    in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6562 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____6562
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____6566 =
                                        let uu____6569 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____6569  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6566;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____6571 =
                                        let uu____6580 =
                                          let uu____6582 =
                                            let uu____6583 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____6583
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____6582]  in
                                        ((false, [lb]), p, uu____6580,
                                          quals1, [])
                                         in
                                      FStar_Syntax_Syntax.Sig_let uu____6571
                                       in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____6508 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____6623 =
  match uu____6623 with
  | (inductive_tps,se) ->
      (match se with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6631,t,uu____6633,n1,quals,uu____6636,uu____6637) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6642 = FStar_Syntax_Util.arrow_formals_comp t  in
           (match uu____6642 with
            | (formals,uu____6650) ->
                (match formals with
                 | [] -> []
                 | uu____6660 ->
                     let filter_records uu___197_6668 =
                       match uu___197_6668 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6670,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6677 -> None  in
                     let fv_qual =
                       let uu____6679 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____6679 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____6686 = FStar_Util.first_N n1 formals  in
                     (match uu____6686 with
                      | (uu____6698,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6712 -> [])
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.binders ->
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
                    let uu____6744 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____6744
                    then
                      let uu____6746 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____6746
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____6749 =
                      let uu____6752 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____6752  in
                    let uu____6753 =
                      let uu____6756 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____6756  in
                    let uu____6757 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6749;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6753;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6757
                    }  in
                  FStar_Syntax_Syntax.Sig_let
                    ((false, [lb]), rng, lids, quals, [])
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun rng  ->
      fun quals  ->
        fun tcs  ->
          let tycon_id uu___198_6790 =
            match uu___198_6790 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6829 =
                  let uu____6830 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____6830  in
                FStar_Parser_AST.mk_term uu____6829 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,_)|FStar_Parser_AST.TVariable a
                ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Syntax_Const.effect_Tot_lid) rng
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
              | Some (FStar_Parser_AST.Implicit ) -> FStar_Parser_AST.Hash
              | uu____6852 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____6855 =
                     let uu____6856 =
                       let uu____6860 = binder_to_term b  in
                       (out, uu____6860, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____6856  in
                   FStar_Parser_AST.mk_term uu____6855
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___199_6867 =
            match uu___199_6867 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____6896  ->
                       match uu____6896 with
                       | (x,t,uu____6903) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____6907 =
                    let uu____6908 =
                      let uu____6909 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____6909  in
                    FStar_Parser_AST.mk_term uu____6908
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____6907 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____6912 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____6924  ->
                          match uu____6924 with
                          | (x,uu____6930,uu____6931) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____6912)
            | uu____6958 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___200_6980 =
            match uu___200_6980 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____6994 = typars_of_binders _env binders  in
                (match uu____6994 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7022 =
                         let uu____7023 =
                           let uu____7024 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7024  in
                         FStar_Parser_AST.mk_term uu____7023
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7022 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       FStar_Syntax_Syntax.Sig_inductive_typ
                         (qlid, [], typars1, k1, mutuals, [], quals1, rng)
                        in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____7035 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7061 =
              FStar_List.fold_left
                (fun uu____7077  ->
                   fun uu____7078  ->
                     match (uu____7077, uu____7078) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7126 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7126 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7061 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7187 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7187
                | uu____7188 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7193 = desugar_abstract_tc quals env [] tc  in
              (match uu____7193 with
               | (uu____7200,uu____7201,se,uu____7203) ->
                   let se1 =
                     match se with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7206,typars,k,[],[],quals1,rng1) ->
                         let quals2 =
                           let uu____7217 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7217
                           then quals1
                           else
                             ((let uu____7222 =
                                 FStar_Range.string_of_range rng1  in
                               let uu____7223 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7222 uu____7223);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7227 ->
                               let uu____7228 =
                                 let uu____7231 =
                                   let uu____7232 =
                                     let uu____7240 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7240)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7232
                                    in
                                 FStar_Syntax_Syntax.mk uu____7231  in
                               uu____7228 None rng1
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, [], t, quals2, rng1)
                     | uu____7251 -> se  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7262 = typars_of_binders env binders  in
              (match uu____7262 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7282 =
                           FStar_Util.for_some
                             (fun uu___201_7283  ->
                                match uu___201_7283 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7284 -> false) quals
                            in
                         if uu____7282
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7290 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___202_7292  ->
                               match uu___202_7292 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7293 -> false))
                        in
                     if uu____7290
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let se =
                     let uu____7299 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7299
                     then
                       let uu____7301 =
                         let uu____7305 =
                           let uu____7306 = unparen t  in
                           uu____7306.FStar_Parser_AST.tm  in
                         match uu____7305 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7318 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7334)::args_rev ->
                                   let uu____7341 =
                                     let uu____7342 = unparen last_arg  in
                                     uu____7342.FStar_Parser_AST.tm  in
                                   (match uu____7341 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7357 -> ([], args))
                               | uu____7362 -> ([], args)  in
                             (match uu____7318 with
                              | (cattributes,args1) ->
                                  let uu____7383 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7383))
                         | uu____7389 -> (t, [])  in
                       match uu____7301 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let uu____7398 =
                             let uu____7408 =
                               FStar_ToSyntax_Env.qualify env id  in
                             let uu____7409 =
                               FStar_All.pipe_right quals1
                                 (FStar_List.filter
                                    (fun uu___203_7413  ->
                                       match uu___203_7413 with
                                       | FStar_Syntax_Syntax.Effect  -> false
                                       | uu____7414 -> true))
                                in
                             (uu____7408, [], typars1, c1, uu____7409,
                               (FStar_List.append cattributes
                                  (FStar_Syntax_Util.comp_flags c1)), rng)
                              in
                           FStar_Syntax_Syntax.Sig_effect_abbrev uu____7398
                     else
                       (let t1 = desugar_typ env' t  in
                        let nm = FStar_ToSyntax_Env.qualify env id  in
                        mk_typ_abbrev nm [] typars k t1 [nm] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7423)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____7436 = tycon_record_as_variant trec  in
              (match uu____7436 with
               | (t,fs) ->
                   let uu____7446 =
                     let uu____7448 =
                       let uu____7449 =
                         let uu____7454 =
                           let uu____7456 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____7456  in
                         (uu____7454, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____7449  in
                     uu____7448 :: quals  in
                   desugar_tycon env rng uu____7446 [t])
          | uu____7459::uu____7460 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____7547 = et  in
                match uu____7547 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7661 ->
                         let trec = tc  in
                         let uu____7674 = tycon_record_as_variant trec  in
                         (match uu____7674 with
                          | (t,fs) ->
                              let uu____7705 =
                                let uu____7707 =
                                  let uu____7708 =
                                    let uu____7713 =
                                      let uu____7715 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____7715  in
                                    (uu____7713, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____7708
                                   in
                                uu____7707 :: quals1  in
                              collect_tcs uu____7705 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7761 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7761 with
                          | (env2,uu____7792,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____7870 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7870 with
                          | (env2,uu____7901,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____7965 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____7989 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____7989 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___205_8227  ->
                             match uu___205_8227 with
                             | FStar_Util.Inr
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (id,uvs,tpars,k,uu____8259,uu____8260,uu____8261,uu____8262),binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8295 =
                                     typars_of_binders env1 binders  in
                                   match uu____8295 with
                                   | (env2,tpars1) ->
                                       let uu____8312 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8312 with
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
                                 let uu____8331 =
                                   let uu____8338 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ([], uu____8338)  in
                                 [uu____8331]
                             | FStar_Util.Inl
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (tname,univs,tpars,k,mutuals1,uu____8363,tags,uu____8365),constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
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
                                 let uu____8418 = push_tparams env1 tpars  in
                                 (match uu____8418 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8453  ->
                                             match uu____8453 with
                                             | (x,uu____8461) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____8466 =
                                        let uu____8477 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8517  ->
                                                  match uu____8517 with
                                                  | (id,topt,uu____8534,of_notation)
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
                                                           | Some t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____8546 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____8546
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___204_8552
                                                                 ->
                                                                match uu___204_8552
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8559
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____8565 =
                                                        let uu____8572 =
                                                          let uu____8573 =
                                                            let uu____8584 =
                                                              let uu____8585
                                                                =
                                                                let uu____8586
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  uu____8586
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                data_tpars
                                                                uu____8585
                                                               in
                                                            (name, univs,
                                                              uu____8584,
                                                              tname, ntps,
                                                              quals2,
                                                              mutuals1, rng)
                                                             in
                                                          FStar_Syntax_Syntax.Sig_datacon
                                                            uu____8573
                                                           in
                                                        (tps, uu____8572)  in
                                                      (name, uu____8565)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8477
                                         in
                                      (match uu____8466 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             (FStar_Syntax_Syntax.Sig_inductive_typ
                                                (tname, univs, tpars, k,
                                                  mutuals1, constrNames,
                                                  tags, rng)))
                                           :: constrs1))
                             | uu____8669 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd)
                      in
                   let uu____8717 =
                     let uu____8721 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____8721 rng
                      in
                   (match uu____8717 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (mk_data_projector_names quals env3))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun uu___206_8755  ->
                                  match uu___206_8755 with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____8758,tps,k,uu____8761,constrs,quals1,uu____8764)
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
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        tname tps k constrs
                                  | uu____8778 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        (env4,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let desugar_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.binder Prims.list)
  =
  fun env  ->
    fun binders  ->
      let uu____8796 =
        FStar_List.fold_left
          (fun uu____8803  ->
             fun b  ->
               match uu____8803 with
               | (env1,binders1) ->
                   let uu____8815 = desugar_binder env1 b  in
                   (match uu____8815 with
                    | (Some a,k) ->
                        let uu____8825 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____8825 with
                         | (env2,a1) ->
                             let uu____8833 =
                               let uu____8835 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___220_8836 = a1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___220_8836.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___220_8836.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    })
                                  in
                               uu____8835 :: binders1  in
                             (env2, uu____8833))
                    | uu____8838 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____8796 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.decl Prims.list ->
                  Prims.bool ->
                    (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
                      Prims.list)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_kind  ->
              fun eff_decls  ->
                fun actions  ->
                  fun for_free  ->
                    let env0 = env  in
                    let monad_env =
                      FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                    let uu____8932 = desugar_binders monad_env eff_binders
                       in
                    match uu____8932 with
                    | (env1,binders) ->
                        let eff_k = desugar_term env1 eff_kind  in
                        let uu____8944 =
                          FStar_All.pipe_right eff_decls
                            (FStar_List.fold_left
                               (fun uu____8955  ->
                                  fun decl  ->
                                    match uu____8955 with
                                    | (env2,out) ->
                                        let uu____8967 =
                                          desugar_decl env2 decl  in
                                        (match uu____8967 with
                                         | (env3,ses) ->
                                             let uu____8975 =
                                               let uu____8977 =
                                                 FStar_List.hd ses  in
                                               uu____8977 :: out  in
                                             (env3, uu____8975))) (env1, []))
                           in
                        (match uu____8944 with
                         | (env2,decls) ->
                             let binders1 =
                               FStar_Syntax_Subst.close_binders binders  in
                             let actions1 =
                               FStar_All.pipe_right actions
                                 (FStar_List.map
                                    (fun d1  ->
                                       match d1.FStar_Parser_AST.d with
                                       | FStar_Parser_AST.Tycon
                                           (uu____8993,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____8995,uu____8996,
                                                         {
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Construct
                                                             (uu____8997,
                                                              (def,uu____8999)::
                                                              (cps_type,uu____9001)::[]);
                                                           FStar_Parser_AST.range
                                                             = uu____9002;
                                                           FStar_Parser_AST.level
                                                             = uu____9003;_}),uu____9004)::[])
                                           when Prims.op_Negation for_free ->
                                           let uu____9030 =
                                             FStar_ToSyntax_Env.qualify env2
                                               name
                                              in
                                           let uu____9031 =
                                             let uu____9032 =
                                               desugar_term env2 def  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9032
                                              in
                                           let uu____9033 =
                                             let uu____9034 =
                                               desugar_typ env2 cps_type  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9034
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9030;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9031;
                                             FStar_Syntax_Syntax.action_typ =
                                               uu____9033
                                           }
                                       | FStar_Parser_AST.Tycon
                                           (uu____9035,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____9037,uu____9038,defn),uu____9040)::[])
                                           when for_free ->
                                           let uu____9057 =
                                             FStar_ToSyntax_Env.qualify env2
                                               name
                                              in
                                           let uu____9058 =
                                             let uu____9059 =
                                               desugar_term env2 defn  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9059
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9057;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9058;
                                             FStar_Syntax_Syntax.action_typ =
                                               FStar_Syntax_Syntax.tun
                                           }
                                       | uu____9060 ->
                                           Prims.raise
                                             (FStar_Errors.Error
                                                ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                  (d1.FStar_Parser_AST.drange)))))
                                in
                             let eff_k1 =
                               FStar_Syntax_Subst.close binders1 eff_k  in
                             let lookup s =
                               let l =
                                 FStar_ToSyntax_Env.qualify env2
                                   (FStar_Ident.mk_ident
                                      (s, (d.FStar_Parser_AST.drange)))
                                  in
                               let uu____9070 =
                                 let uu____9071 =
                                   FStar_ToSyntax_Env.fail_or env2
                                     (FStar_ToSyntax_Env.try_lookup_definition
                                        env2) l
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close binders1)
                                   uu____9071
                                  in
                               ([], uu____9070)  in
                             let mname =
                               FStar_ToSyntax_Env.qualify env0 eff_name  in
                             let qualifiers =
                               FStar_List.map
                                 (trans_qual d.FStar_Parser_AST.drange
                                    (Some mname)) quals
                                in
                             let se =
                               if for_free
                               then
                                 let dummy_tscheme =
                                   let uu____9083 =
                                     FStar_Syntax_Syntax.mk
                                       FStar_Syntax_Syntax.Tm_unknown None
                                       FStar_Range.dummyRange
                                      in
                                   ([], uu____9083)  in
                                 let uu____9093 =
                                   let uu____9096 =
                                     let uu____9097 =
                                       let uu____9098 = lookup "repr"  in
                                       Prims.snd uu____9098  in
                                     let uu____9103 = lookup "return"  in
                                     let uu____9104 = lookup "bind"  in
                                     {
                                       FStar_Syntax_Syntax.qualifiers =
                                         qualifiers;
                                       FStar_Syntax_Syntax.cattributes = [];
                                       FStar_Syntax_Syntax.mname = mname;
                                       FStar_Syntax_Syntax.univs = [];
                                       FStar_Syntax_Syntax.binders = binders1;
                                       FStar_Syntax_Syntax.signature = eff_k1;
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
                                       FStar_Syntax_Syntax.repr = uu____9097;
                                       FStar_Syntax_Syntax.return_repr =
                                         uu____9103;
                                       FStar_Syntax_Syntax.bind_repr =
                                         uu____9104;
                                       FStar_Syntax_Syntax.actions = actions1
                                     }  in
                                   (uu____9096, (d.FStar_Parser_AST.drange))
                                    in
                                 FStar_Syntax_Syntax.Sig_new_effect_for_free
                                   uu____9093
                               else
                                 (let rr =
                                    (FStar_All.pipe_right qualifiers
                                       (FStar_List.contains
                                          FStar_Syntax_Syntax.Reifiable))
                                      ||
                                      (FStar_All.pipe_right qualifiers
                                         FStar_Syntax_Syntax.contains_reflectable)
                                     in
                                  let un_ts = ([], FStar_Syntax_Syntax.tun)
                                     in
                                  let uu____9114 =
                                    let uu____9117 =
                                      let uu____9118 = lookup "return_wp"  in
                                      let uu____9119 = lookup "bind_wp"  in
                                      let uu____9120 = lookup "if_then_else"
                                         in
                                      let uu____9121 = lookup "ite_wp"  in
                                      let uu____9122 = lookup "stronger"  in
                                      let uu____9123 = lookup "close_wp"  in
                                      let uu____9124 = lookup "assert_p"  in
                                      let uu____9125 = lookup "assume_p"  in
                                      let uu____9126 = lookup "null_wp"  in
                                      let uu____9127 = lookup "trivial"  in
                                      let uu____9128 =
                                        if rr
                                        then
                                          let uu____9129 = lookup "repr"  in
                                          FStar_All.pipe_left Prims.snd
                                            uu____9129
                                        else FStar_Syntax_Syntax.tun  in
                                      let uu____9138 =
                                        if rr then lookup "return" else un_ts
                                         in
                                      let uu____9140 =
                                        if rr then lookup "bind" else un_ts
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          qualifiers;
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.signature =
                                          eff_k1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____9118;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____9119;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____9120;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____9121;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____9122;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____9123;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____9124;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____9125;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____9126;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____9127;
                                        FStar_Syntax_Syntax.repr = uu____9128;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9138;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9140;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    (uu____9117, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Syntax_Syntax.Sig_new_effect
                                    uu____9114)
                                in
                             let env3 =
                               FStar_ToSyntax_Env.push_sigelt env0 se  in
                             let env4 =
                               FStar_All.pipe_right actions1
                                 (FStar_List.fold_left
                                    (fun env4  ->
                                       fun a  ->
                                         let uu____9147 =
                                           FStar_Syntax_Util.action_as_lb
                                             mname a
                                            in
                                         FStar_ToSyntax_Env.push_sigelt env4
                                           uu____9147) env3)
                                in
                             let env5 =
                               let uu____9149 =
                                 FStar_All.pipe_right quals
                                   (FStar_List.contains
                                      FStar_Parser_AST.Reflectable)
                                  in
                               if uu____9149
                               then
                                 let reflect_lid =
                                   FStar_All.pipe_right
                                     (FStar_Ident.id_of_text "reflect")
                                     (FStar_ToSyntax_Env.qualify monad_env)
                                    in
                                 let refl_decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (reflect_lid, [],
                                       FStar_Syntax_Syntax.tun,
                                       [FStar_Syntax_Syntax.Assumption;
                                       FStar_Syntax_Syntax.Reflectable mname],
                                       (d.FStar_Parser_AST.drange))
                                    in
                                 FStar_ToSyntax_Env.push_sigelt env4
                                   refl_decl
                               else env4  in
                             (env5, [se]))

and desugar_redefine_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident Prims.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_Syntax.eff_decl ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
                  ->
                  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
                    Prims.list)
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                fun build_sigelt  ->
                  let env0 = env  in
                  let env1 =
                    FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                  let uu____9177 = desugar_binders env1 eff_binders  in
                  match uu____9177 with
                  | (env2,binders) ->
                      let uu____9188 =
                        let uu____9197 = head_and_args defn  in
                        match uu____9197 with
                        | (head1,args) ->
                            let ed =
                              match head1.FStar_Parser_AST.tm with
                              | FStar_Parser_AST.Name l ->
                                  FStar_ToSyntax_Env.fail_or env2
                                    (FStar_ToSyntax_Env.try_lookup_effect_defn
                                       env2) l
                              | uu____9221 ->
                                  let uu____9222 =
                                    let uu____9223 =
                                      let uu____9226 =
                                        let uu____9227 =
                                          let uu____9228 =
                                            FStar_Parser_AST.term_to_string
                                              head1
                                             in
                                          Prims.strcat uu____9228
                                            " not found"
                                           in
                                        Prims.strcat "Effect " uu____9227  in
                                      (uu____9226,
                                        (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Errors.Error uu____9223  in
                                  Prims.raise uu____9222
                               in
                            let uu____9229 =
                              match FStar_List.rev args with
                              | (last_arg,uu____9245)::args_rev ->
                                  let uu____9252 =
                                    let uu____9253 = unparen last_arg  in
                                    uu____9253.FStar_Parser_AST.tm  in
                                  (match uu____9252 with
                                   | FStar_Parser_AST.Attributes ts ->
                                       (ts, (FStar_List.rev args_rev))
                                   | uu____9268 -> ([], args))
                              | uu____9273 -> ([], args)  in
                            (match uu____9229 with
                             | (cattributes,args1) ->
                                 let uu____9299 = desugar_args env2 args1  in
                                 let uu____9304 =
                                   desugar_attributes env2 cattributes  in
                                 (ed, uu____9299, uu____9304))
                         in
                      (match uu____9188 with
                       | (ed,args,cattributes) ->
                           let binders1 =
                             FStar_Syntax_Subst.close_binders binders  in
                           let sub1 uu____9337 =
                             match uu____9337 with
                             | (uu____9344,x) ->
                                 let uu____9348 =
                                   FStar_Syntax_Subst.open_term
                                     ed.FStar_Syntax_Syntax.binders x
                                    in
                                 (match uu____9348 with
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
                                            args
                                           in
                                        let uu____9368 =
                                          let uu____9369 =
                                            FStar_Syntax_Subst.subst s x1  in
                                          FStar_Syntax_Subst.close binders1
                                            uu____9369
                                           in
                                        ([], uu____9368))))
                              in
                           let mname =
                             FStar_ToSyntax_Env.qualify env0 eff_name  in
                           let ed1 =
                             let uu____9373 =
                               let uu____9375 = trans_qual1 (Some mname)  in
                               FStar_List.map uu____9375 quals  in
                             let uu____9378 =
                               let uu____9379 =
                                 sub1
                                   ([], (ed.FStar_Syntax_Syntax.signature))
                                  in
                               Prims.snd uu____9379  in
                             let uu____9385 =
                               sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                             let uu____9386 =
                               sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                             let uu____9387 =
                               sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                             let uu____9388 =
                               sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                             let uu____9389 =
                               sub1 ed.FStar_Syntax_Syntax.stronger  in
                             let uu____9390 =
                               sub1 ed.FStar_Syntax_Syntax.close_wp  in
                             let uu____9391 =
                               sub1 ed.FStar_Syntax_Syntax.assert_p  in
                             let uu____9392 =
                               sub1 ed.FStar_Syntax_Syntax.assume_p  in
                             let uu____9393 =
                               sub1 ed.FStar_Syntax_Syntax.null_wp  in
                             let uu____9394 =
                               sub1 ed.FStar_Syntax_Syntax.trivial  in
                             let uu____9395 =
                               let uu____9396 =
                                 sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                               Prims.snd uu____9396  in
                             let uu____9402 =
                               sub1 ed.FStar_Syntax_Syntax.return_repr  in
                             let uu____9403 =
                               sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                             let uu____9404 =
                               FStar_List.map
                                 (fun action  ->
                                    let uu____9407 =
                                      FStar_ToSyntax_Env.qualify env2
                                        action.FStar_Syntax_Syntax.action_unqualified_name
                                       in
                                    let uu____9408 =
                                      let uu____9409 =
                                        sub1
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_defn))
                                         in
                                      Prims.snd uu____9409  in
                                    let uu____9415 =
                                      let uu____9416 =
                                        sub1
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_typ))
                                         in
                                      Prims.snd uu____9416  in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        uu____9407;
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (action.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        (action.FStar_Syntax_Syntax.action_univs);
                                      FStar_Syntax_Syntax.action_defn =
                                        uu____9408;
                                      FStar_Syntax_Syntax.action_typ =
                                        uu____9415
                                    }) ed.FStar_Syntax_Syntax.actions
                                in
                             {
                               FStar_Syntax_Syntax.qualifiers = uu____9373;
                               FStar_Syntax_Syntax.cattributes = cattributes;
                               FStar_Syntax_Syntax.mname = mname;
                               FStar_Syntax_Syntax.univs = [];
                               FStar_Syntax_Syntax.binders = binders1;
                               FStar_Syntax_Syntax.signature = uu____9378;
                               FStar_Syntax_Syntax.ret_wp = uu____9385;
                               FStar_Syntax_Syntax.bind_wp = uu____9386;
                               FStar_Syntax_Syntax.if_then_else = uu____9387;
                               FStar_Syntax_Syntax.ite_wp = uu____9388;
                               FStar_Syntax_Syntax.stronger = uu____9389;
                               FStar_Syntax_Syntax.close_wp = uu____9390;
                               FStar_Syntax_Syntax.assert_p = uu____9391;
                               FStar_Syntax_Syntax.assume_p = uu____9392;
                               FStar_Syntax_Syntax.null_wp = uu____9393;
                               FStar_Syntax_Syntax.trivial = uu____9394;
                               FStar_Syntax_Syntax.repr = uu____9395;
                               FStar_Syntax_Syntax.return_repr = uu____9402;
                               FStar_Syntax_Syntax.bind_repr = uu____9403;
                               FStar_Syntax_Syntax.actions = uu____9404
                             }  in
                           let se =
                             build_sigelt ed1 d.FStar_Parser_AST.drange  in
                           let monad_env = env2  in
                           let env3 = FStar_ToSyntax_Env.push_sigelt env0 se
                              in
                           let env4 =
                             FStar_All.pipe_right
                               ed1.FStar_Syntax_Syntax.actions
                               (FStar_List.fold_left
                                  (fun env4  ->
                                     fun a  ->
                                       let uu____9429 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env4
                                         uu____9429) env3)
                              in
                           let env5 =
                             let uu____9431 =
                               FStar_All.pipe_right quals
                                 (FStar_List.contains
                                    FStar_Parser_AST.Reflectable)
                                in
                             if uu____9431
                             then
                               let reflect_lid =
                                 FStar_All.pipe_right
                                   (FStar_Ident.id_of_text "reflect")
                                   (FStar_ToSyntax_Env.qualify monad_env)
                                  in
                               let refl_decl =
                                 FStar_Syntax_Syntax.Sig_declare_typ
                                   (reflect_lid, [], FStar_Syntax_Syntax.tun,
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname],
                                     (d.FStar_Parser_AST.drange))
                                  in
                               FStar_ToSyntax_Env.push_sigelt env4 refl_decl
                             else env4  in
                           (env5, [se]))

and desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            FStar_Syntax_Syntax.Sig_pragma
              ((trans_pragma p), (d.FStar_Parser_AST.drange))
             in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____9456 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____9468 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____9468, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____9489  -> match uu____9489 with | (x,uu____9494) -> x)
              tcs
             in
          let uu____9497 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d.FStar_Parser_AST.drange uu____9497 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env) attrs  in
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
               | (p,uu____9536)::[] ->
                   let uu____9541 = is_app_pattern p  in
                   Prims.op_Negation uu____9541
               | uu____9542 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____9553 =
              let uu____9554 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____9554.FStar_Syntax_Syntax.n  in
            (match uu____9553 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____9560) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____9580::uu____9581 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____9583 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___207_9587  ->
                               match uu___207_9587 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____9589;
                                   FStar_Syntax_Syntax.lbunivs = uu____9590;
                                   FStar_Syntax_Syntax.lbtyp = uu____9591;
                                   FStar_Syntax_Syntax.lbeff = uu____9592;
                                   FStar_Syntax_Syntax.lbdef = uu____9593;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____9600;
                                   FStar_Syntax_Syntax.lbtyp = uu____9601;
                                   FStar_Syntax_Syntax.lbeff = uu____9602;
                                   FStar_Syntax_Syntax.lbdef = uu____9603;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____9615 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____9621  ->
                             match uu____9621 with
                             | (uu____9624,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____9615
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____9632 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____9632
                   then
                     let uu____9637 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___221_9644 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___222_9645 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___222_9645.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___222_9645.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___221_9644.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___221_9644.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___221_9644.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___221_9644.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), uu____9637)
                   else lbs  in
                 let s =
                   let uu____9653 =
                     let uu____9662 =
                       FStar_All.pipe_right fvs
                         (FStar_List.map
                            (fun fv  ->
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                        in
                     (lbs1, (d.FStar_Parser_AST.drange), uu____9662, quals2,
                       attrs1)
                      in
                   FStar_Syntax_Syntax.Sig_let uu____9653  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 (env1, [s])
             | uu____9679 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____9683 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____9694 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____9683 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar (fresh_toplevel_name, None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___223_9710 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___223_9710.FStar_Parser_AST.prange)
                       }
                   | uu____9711 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___224_9715 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___224_9715.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___224_9715.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___224_9715.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____9734 id =
                   match uu____9734 with
                   | (env1,ses) ->
                       let main =
                         let uu____9747 =
                           let uu____9748 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____9748  in
                         FStar_Parser_AST.mk_term uu____9747
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main, [(pat, None, projectee)]))
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (id, None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____9776 = desugar_decl env1 id_decl  in
                       (match uu____9776 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____9787 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____9787 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            FStar_Syntax_Syntax.Sig_main (e, (d.FStar_Parser_AST.drange))  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let uu____9801 =
            let uu____9803 =
              let uu____9804 =
                let uu____9810 = FStar_ToSyntax_Env.qualify env id  in
                (uu____9810, f, [FStar_Syntax_Syntax.Assumption],
                  (d.FStar_Parser_AST.drange))
                 in
              FStar_Syntax_Syntax.Sig_assume uu____9804  in
            [uu____9803]  in
          (env, uu____9801)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____9817 = close_fun env t  in desugar_term env uu____9817
             in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let se =
            let uu____9823 =
              let uu____9830 = FStar_ToSyntax_Env.qualify env id  in
              let uu____9831 = FStar_List.map (trans_qual1 None) quals1  in
              (uu____9830, [], t1, uu____9831, (d.FStar_Parser_AST.drange))
               in
            FStar_Syntax_Syntax.Sig_declare_typ uu____9823  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____9839 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____9839 with
           | (t,uu____9847) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let se =
                 FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid],
                     (d.FStar_Parser_AST.drange))
                  in
               let se' =
                 FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], 
                     [l], (d.FStar_Parser_AST.drange))
                  in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let data_ops = mk_data_projector_names [] env1 ([], se)  in
               let discs =
                 mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l]
                  in
               let env2 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
                   (FStar_List.append discs data_ops)
                  in
               (env2, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____9872 =
              let uu____9873 = FStar_Syntax_Syntax.null_binder t  in
              [uu____9873]  in
            let uu____9874 =
              let uu____9875 =
                let uu____9876 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                Prims.fst uu____9876  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____9875  in
            FStar_Syntax_Util.arrow uu____9872 uu____9874  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let se =
            FStar_Syntax_Syntax.Sig_datacon
              (l, [], t1, FStar_Syntax_Const.exn_lid, (Prims.parse_int "0"),
                [FStar_Syntax_Syntax.ExceptionConstructor],
                [FStar_Syntax_Const.exn_lid], (d.FStar_Parser_AST.drange))
             in
          let se' =
            FStar_Syntax_Syntax.Sig_bundle
              ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l],
                (d.FStar_Parser_AST.drange))
             in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env1 ([], se)  in
          let discs =
            mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l]
             in
          let env2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
              (FStar_List.append discs data_ops)
             in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
            (fun ed  ->
               fun range  -> FStar_Syntax_Syntax.Sig_new_effect (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
            (fun ed  ->
               fun range  ->
                 FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions true
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions false
      | FStar_Parser_AST.SubEffect l ->
          let src =
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (l.FStar_Parser_AST.msource);
              FStar_Syntax_Syntax.comp_univs = [];
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = []
            }  in
          let dst =
            {
              FStar_Syntax_Syntax.comp_typ_name = (l.FStar_Parser_AST.mdest);
              FStar_Syntax_Syntax.comp_univs = [];
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = []
            }  in
          let uu____9951 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____9961 =
                  let uu____9963 = desugar_term env t  in Some uu____9963  in
                (uu____9961, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____9968 =
                  let uu____9970 = desugar_term env wp  in Some uu____9970
                   in
                let uu____9971 =
                  let uu____9973 = desugar_term env t  in Some uu____9973  in
                (uu____9968, uu____9971)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____9977 =
                  let uu____9979 = desugar_term env t  in Some uu____9979  in
                (None, uu____9977)
             in
          (match uu____9951 with
           | (lift_wp,lift) ->
               let se =
                 FStar_Syntax_Syntax.Sig_sub_effect
                   ({
                      FStar_Syntax_Syntax.sub_eff_univs = [];
                      FStar_Syntax_Syntax.sub_eff_binders = [];
                      FStar_Syntax_Syntax.sub_eff_source = src;
                      FStar_Syntax_Syntax.sub_eff_target = dst;
                      FStar_Syntax_Syntax.sub_eff_lift_wp = lift_wp;
                      FStar_Syntax_Syntax.sub_eff_lift = lift
                    }, (d.FStar_Parser_AST.drange))
                  in
               (env, [se]))

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10007  ->
           fun d  ->
             match uu____10007 with
             | (env1,sigelts) ->
                 let uu____10019 = desugar_decl env1 d  in
                 (match uu____10019 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
  
let open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Syntax_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Syntax_Const.all_lid)
    FStar_Range.dummyRange]
  
let desugar_modul_common :
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (None ,uu____10061) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10064;
               FStar_Syntax_Syntax.exports = uu____10065;
               FStar_Syntax_Syntax.is_interface = uu____10066;_},FStar_Parser_AST.Module
             (current_lid,uu____10068)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10073) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____10075 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10095 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____10095, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10105 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____10105, mname, decls, false)
           in
        match uu____10075 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10123 = desugar_decls env2 decls  in
            (match uu____10123 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____10148 =
            (FStar_Options.interactive ()) &&
              (let uu____10149 =
                 let uu____10150 =
                   let uu____10151 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____10151  in
                 FStar_Util.get_file_extension uu____10150  in
               uu____10149 = "fsti")
             in
          if uu____10148
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10159,uu____10160) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m  in
        let uu____10164 = desugar_modul_common curmod env m1  in
        match uu____10164 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10174 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10186 = desugar_modul_common None env m  in
      match uu____10186 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____10197 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10197
            then
              let uu____10198 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____10198
            else ());
           (let uu____10200 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____10200, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10211 =
        FStar_List.fold_left
          (fun uu____10218  ->
             fun m  ->
               match uu____10218 with
               | (env1,mods) ->
                   let uu____10230 = desugar_modul env1 m  in
                   (match uu____10230 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____10211 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10254 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____10254 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___225_10260 = en1  in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___225_10260.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___225_10260.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___225_10260.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___225_10260.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___225_10260.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___225_10260.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___225_10260.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___225_10260.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___225_10260.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___225_10260.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___225_10260.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  