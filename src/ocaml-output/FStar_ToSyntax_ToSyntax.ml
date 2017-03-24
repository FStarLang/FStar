open Prims
let trans_aqual :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___185_5  ->
    match uu___185_5 with
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
      fun uu___186_19  ->
        match uu___186_19 with
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
  fun uu___187_25  ->
    match uu___187_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___188_32  ->
    match uu___188_32 with
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
  fun uu___189_750  ->
    match uu___189_750 with
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
      fun uu___190_772  ->
        match uu___190_772 with
        | (None ,k) ->
            let uu____781 = FStar_Syntax_Syntax.null_binder k  in
            (uu____781, env)
        | (Some a,k) ->
            let uu____785 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____785 with
             | (env1,a1) ->
                 (((let uu___212_796 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___212_796.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___212_796.FStar_Syntax_Syntax.index);
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
  fun uu___191_1056  ->
    match uu___191_1056 with
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
                  (fun uu___192_1182  ->
                     match uu___192_1182 with
                     | FStar_Util.Inr uu____1185 -> true
                     | uu____1186 -> false) univargs
              then
                let uu____1189 =
                  let uu____1190 =
                    FStar_List.map
                      (fun uu___193_1194  ->
                         match uu___193_1194 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1190  in
                FStar_Util.Inr uu____1189
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___194_1204  ->
                        match uu___194_1204 with
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1448,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1470  ->
                          match uu____1470 with
                          | (p3,uu____1476) ->
                              let uu____1477 = pat_vars p3  in
                              FStar_Util.set_union out uu____1477)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1  in
                let uu____1491 =
                  let uu____1492 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3  in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1
                     in
                  Prims.op_Negation uu____1492  in
                if uu____1491
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
         | (true ,uu____1499) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1527 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1527 with
           | Some y -> (l, e, y)
           | uu____1535 ->
               let uu____1537 = push_bv_maybe_mut e x  in
               (match uu____1537 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
               let uu____1586 =
                 let uu____1587 =
                   let uu____1588 =
                     let uu____1592 =
                       let uu____1593 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op
                          in
                       FStar_Ident.id_of_text uu____1593  in
                     (uu____1592, None)  in
                   FStar_Parser_AST.PatVar uu____1588  in
                 {
                   FStar_Parser_AST.pat = uu____1587;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1586
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1605 = aux loc env1 p2  in
               (match uu____1605 with
                | (loc1,env2,var,p3,uu____1624) ->
                    let uu____1629 =
                      FStar_List.fold_left
                        (fun uu____1642  ->
                           fun p4  ->
                             match uu____1642 with
                             | (loc2,env3,ps1) ->
                                 let uu____1665 = aux loc2 env3 p4  in
                                 (match uu____1665 with
                                  | (loc3,env4,uu____1681,p5,uu____1683) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____1629 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1)))
                            in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1727 = aux loc env1 p2  in
               (match uu____1727 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1752 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1758 = close_fun env1 t  in
                            desugar_term env1 uu____1758  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1760 -> true)
                           then
                             (let uu____1761 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1762 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1763 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1761 uu____1762 uu____1763)
                           else ();
                           LocalBinder
                             (((let uu___213_1765 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___213_1765.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___213_1765.FStar_Syntax_Syntax.index);
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
               let uu____1769 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1769, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1779 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1779, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1797 = resolvex loc env1 x  in
               (match uu____1797 with
                | (loc1,env2,xbv) ->
                    let uu____1811 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1811, imp))
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
               let uu____1822 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1822, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1840;_},args)
               ->
               let uu____1844 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1862  ->
                        match uu____1862 with
                        | (loc1,env2,args1) ->
                            let uu____1892 = aux loc1 env2 arg  in
                            (match uu____1892 with
                             | (loc2,env3,uu____1910,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1844 with
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
                    let uu____1959 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____1959, false))
           | FStar_Parser_AST.PatApp uu____1972 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1985 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____1999  ->
                        match uu____1999 with
                        | (loc1,env2,pats1) ->
                            let uu____2021 = aux loc1 env2 pat  in
                            (match uu____2021 with
                             | (loc2,env3,uu____2037,pat1,uu____2039) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____1985 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2073 =
                        let uu____2076 =
                          let uu____2081 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2081  in
                        let uu____2082 =
                          let uu____2083 =
                            let uu____2091 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2091, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2083  in
                        FStar_All.pipe_left uu____2076 uu____2082  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2114 =
                               let uu____2115 =
                                 let uu____2123 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2123, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2115  in
                             FStar_All.pipe_left (pos_r r) uu____2114) pats1
                        uu____2073
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2155 =
                 FStar_List.fold_left
                   (fun uu____2172  ->
                      fun p2  ->
                        match uu____2172 with
                        | (loc1,env2,pats) ->
                            let uu____2203 = aux loc1 env2 p2  in
                            (match uu____2203 with
                             | (loc2,env3,uu____2221,pat,uu____2223) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2155 with
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
                    let uu____2294 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2294 with
                     | (constr,uu____2307) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2310 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2312 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2312,
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
                      (fun uu____2353  ->
                         match uu____2353 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2368  ->
                         match uu____2368 with
                         | (f,uu____2372) ->
                             let uu____2373 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2385  ->
                                       match uu____2385 with
                                       | (g,uu____2389) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2373 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2392,p2) -> p2)))
                  in
               let app =
                 let uu____2397 =
                   let uu____2398 =
                     let uu____2402 =
                       let uu____2403 =
                         let uu____2404 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2404  in
                       FStar_Parser_AST.mk_pattern uu____2403
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2402, args)  in
                   FStar_Parser_AST.PatApp uu____2398  in
                 FStar_Parser_AST.mk_pattern uu____2397
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2406 = aux loc env1 app  in
               (match uu____2406 with
                | (env2,e,b,p2,uu____2425) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2447 =
                            let uu____2448 =
                              let uu____2456 =
                                let uu___214_2457 = fv  in
                                let uu____2458 =
                                  let uu____2460 =
                                    let uu____2461 =
                                      let uu____2465 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2465)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2461
                                     in
                                  Some uu____2460  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___214_2457.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___214_2457.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2458
                                }  in
                              (uu____2456, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2448  in
                          FStar_All.pipe_left pos uu____2447
                      | uu____2484 -> p2  in
                    (env2, e, b, p3, false))
            in
         let uu____2487 = aux [] env p  in
         match uu____2487 with
         | (uu____2498,env1,b,p1,uu____2502) ->
             ((let uu____2508 = check_linear_pattern_variables p1  in
               FStar_All.pipe_left Prims.ignore uu____2508);
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
            let uu____2527 =
              let uu____2528 =
                let uu____2531 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2531, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2528  in
            (env, uu____2527, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2542 =
                  let uu____2543 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x  in
                  FStar_Ident.id_of_text uu____2543  in
                mklet uu____2542
            | FStar_Parser_AST.PatVar (x,uu____2545) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2549);
                   FStar_Parser_AST.prange = uu____2550;_},t)
                ->
                let uu____2554 =
                  let uu____2555 =
                    let uu____2558 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2559 = desugar_term env t  in
                    (uu____2558, uu____2559)  in
                  LetBinder uu____2555  in
                (env, uu____2554, None)
            | uu____2561 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2567 = desugar_data_pat env p is_mut  in
             match uu____2567 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2583 -> Some p1  in
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
  fun uu____2587  ->
    fun env  ->
      fun pat  ->
        let uu____2590 = desugar_data_pat env pat false  in
        match uu____2590 with | (env1,uu____2597,pat1) -> (env1, pat1)

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
        let uu___215_2604 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___215_2604.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___215_2604.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___215_2604.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___215_2604.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___215_2604.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___215_2604.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___215_2604.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___215_2604.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___215_2604.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___215_2604.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___215_2604.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        }  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___216_2608 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___216_2608.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___216_2608.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___216_2608.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___216_2608.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___216_2608.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___216_2608.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___216_2608.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___216_2608.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___216_2608.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___216_2608.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___216_2608.FStar_ToSyntax_Env.admitted_iface);
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
      fun uu____2611  ->
        fun range  ->
          match uu____2611 with
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
                let uu____2622 = FStar_ToSyntax_Env.try_lookup_lid env lid1
                   in
                match uu____2622 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2633 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1)
                       in
                    failwith uu____2633
                 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              let uu____2650 =
                let uu____2653 =
                  let uu____2654 =
                    let uu____2664 =
                      let uu____2670 =
                        let uu____2675 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____2675)  in
                      [uu____2670]  in
                    (lid2, uu____2664)  in
                  FStar_Syntax_Syntax.Tm_app uu____2654  in
                FStar_Syntax_Syntax.mk uu____2653  in
              uu____2650 None range

and desugar_name :
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
            let uu____2710 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____2710 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____2728 =
                    let uu____2729 =
                      let uu____2734 = mk_ref_read tm1  in
                      (uu____2734,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____2729  in
                  FStar_All.pipe_left mk1 uu____2728
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2748 =
          let uu____2749 = unparen t  in uu____2749.FStar_Parser_AST.tm  in
        match uu____2748 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2750; FStar_Ident.ident = uu____2751;
              FStar_Ident.nsstr = uu____2752; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2754 ->
            let uu____2755 =
              let uu____2756 =
                let uu____2759 =
                  let uu____2760 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____2760  in
                (uu____2759, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____2756  in
            Prims.raise uu____2755
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
          let uu___217_2788 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___217_2788.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___217_2788.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___217_2788.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2795 =
          let uu____2796 = unparen top  in uu____2796.FStar_Parser_AST.tm  in
        match uu____2795 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2797 -> desugar_formula env top
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
        | FStar_Parser_AST.Op ("*",uu____2826::uu____2827::[]) when
            let uu____2829 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*"
               in
            FStar_All.pipe_right uu____2829 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2841 = flatten1 t1  in
                  FStar_List.append uu____2841 [t2]
              | uu____2843 -> [t]  in
            let targs =
              let uu____2846 =
                let uu____2848 = unparen top  in flatten1 uu____2848  in
              FStar_All.pipe_right uu____2846
                (FStar_List.map
                   (fun t  ->
                      let uu____2852 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____2852))
               in
            let uu____2853 =
              let uu____2856 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2856
               in
            (match uu____2853 with
             | (tup,uu____2863) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2866 =
              let uu____2869 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              Prims.fst uu____2869  in
            FStar_All.pipe_left setpos uu____2866
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2883 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2883 with
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
                             let uu____2905 = desugar_term env t  in
                             (uu____2905, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2912; FStar_Ident.ident = uu____2913;
              FStar_Ident.nsstr = uu____2914; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2916; FStar_Ident.ident = uu____2917;
              FStar_Ident.nsstr = uu____2918; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2920; FStar_Ident.ident = uu____2921;
               FStar_Ident.nsstr = uu____2922; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2932 =
              let uu____2933 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____2933  in
            mk1 uu____2932
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2934; FStar_Ident.ident = uu____2935;
              FStar_Ident.nsstr = uu____2936; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2938; FStar_Ident.ident = uu____2939;
              FStar_Ident.nsstr = uu____2940; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2942; FStar_Ident.ident = uu____2943;
              FStar_Ident.nsstr = uu____2944; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2948;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2949 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
            (match uu____2949 with
             | Some ed ->
                 let uu____2952 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2952
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  ->
                 let uu____2953 =
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     (FStar_Ident.text_of_lid eff_name) txt
                    in
                 failwith uu____2953)
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____2957 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2957 with
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
              let uu____2973 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____2973 with
              | Some uu____2978 -> Some (true, l)
              | None  ->
                  let uu____2981 =
                    FStar_ToSyntax_Env.try_lookup_root_effect_name env l  in
                  (match uu____2981 with
                   | Some new_name -> Some (false, new_name)
                   | uu____2989 -> None)
               in
            (match name with
             | Some (resolve,new_name) ->
                 let uu____2997 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     new_name i
                    in
                 desugar_name mk1 setpos env resolve uu____2997
             | uu____2998 ->
                 let uu____3002 =
                   let uu____3003 =
                     let uu____3006 =
                       FStar_Util.format1
                         "Data constructor or effect %s not found"
                         l.FStar_Ident.str
                        in
                     (uu____3006, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____3003  in
                 Prims.raise uu____3002)
        | FStar_Parser_AST.Discrim lid ->
            let uu____3008 = FStar_ToSyntax_Env.try_lookup_datacon env lid
               in
            (match uu____3008 with
             | None  ->
                 let uu____3010 =
                   let uu____3011 =
                     let uu____3014 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str
                        in
                     (uu____3014, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____3011  in
                 Prims.raise uu____3010
             | uu____3015 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 desugar_name mk1 setpos env true lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3026 = FStar_ToSyntax_Env.try_lookup_datacon env l  in
            (match uu____3026 with
             | Some head1 ->
                 let uu____3029 =
                   let uu____3034 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                      in
                   (uu____3034, true)  in
                 (match uu____3029 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3047 ->
                           let uu____3051 =
                             FStar_Util.take
                               (fun uu____3062  ->
                                  match uu____3062 with
                                  | (uu____3065,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args
                              in
                           (match uu____3051 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes
                                   in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3098  ->
                                       match uu____3098 with
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
            let uu____3133 =
              FStar_List.fold_left
                (fun uu____3150  ->
                   fun b  ->
                     match uu____3150 with
                     | (env1,tparams,typs) ->
                         let uu____3181 = desugar_binder env1 b  in
                         (match uu____3181 with
                          | (xopt,t1) ->
                              let uu____3197 =
                                match xopt with
                                | None  ->
                                    let uu____3202 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3202)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3197 with
                               | (env2,x) ->
                                   let uu____3214 =
                                     let uu____3216 =
                                       let uu____3218 =
                                         let uu____3219 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3219
                                          in
                                       [uu____3218]  in
                                     FStar_List.append typs uu____3216  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___218_3232 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___218_3232.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___218_3232.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3214))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3133 with
             | (env1,uu____3245,targs) ->
                 let uu____3257 =
                   let uu____3260 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3260
                    in
                 (match uu____3257 with
                  | (tup,uu____3267) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3275 = uncurry binders t  in
            (match uu____3275 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___195_3298 =
                   match uu___195_3298 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3308 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3308
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3324 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3324 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3335 = desugar_binder env b  in
            (match uu____3335 with
             | (None ,uu____3339) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3345 = as_binder env None b1  in
                 (match uu____3345 with
                  | ((x,uu____3349),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3354 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3354))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3369 =
              FStar_List.fold_left
                (fun uu____3376  ->
                   fun pat  ->
                     match uu____3376 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3391,t) ->
                              let uu____3393 =
                                let uu____3395 = free_type_vars env1 t  in
                                FStar_List.append uu____3395 ftvs  in
                              (env1, uu____3393)
                          | uu____3398 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3369 with
             | (uu____3401,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3409 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3409 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___196_3438 =
                   match uu___196_3438 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3467 =
                                 let uu____3468 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3468
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3467 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3510 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3510
                   | p::rest ->
                       let uu____3518 = desugar_binding_pat env1 p  in
                       (match uu____3518 with
                        | (env2,b,pat) ->
                            let uu____3530 =
                              match b with
                              | LetBinder uu____3549 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3580) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3603 =
                                          let uu____3606 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____3606, p1)  in
                                        Some uu____3603
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3631,uu____3632) ->
                                             let tup2 =
                                               let uu____3634 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3634
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3638 =
                                                 let uu____3641 =
                                                   let uu____3642 =
                                                     let uu____3652 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____3655 =
                                                       let uu____3657 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____3658 =
                                                         let uu____3660 =
                                                           let uu____3661 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3661
                                                            in
                                                         [uu____3660]  in
                                                       uu____3657 ::
                                                         uu____3658
                                                        in
                                                     (uu____3652, uu____3655)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3642
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3641
                                                  in
                                               uu____3638 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____3676 =
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
                                                 uu____3676
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3696,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3698,pats)) ->
                                             let tupn =
                                               let uu____3725 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3725
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3735 =
                                                 let uu____3736 =
                                                   let uu____3746 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____3749 =
                                                     let uu____3755 =
                                                       let uu____3761 =
                                                         let uu____3762 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3762
                                                          in
                                                       [uu____3761]  in
                                                     FStar_List.append args
                                                       uu____3755
                                                      in
                                                   (uu____3746, uu____3749)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3736
                                                  in
                                               mk1 uu____3735  in
                                             let p2 =
                                               let uu____3777 =
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
                                                 uu____3777
                                                in
                                             Some (sc1, p2)
                                         | uu____3801 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3530 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var a;
               FStar_Parser_AST.range = rng;
               FStar_Parser_AST.level = uu____3844;_},phi,uu____3846)
            when
            (FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
              (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)
            ->
            let phi1 = desugar_formula env phi  in
            let a1 = FStar_Ident.set_lid_range a rng  in
            let uu____3849 =
              let uu____3850 =
                let uu____3860 =
                  FStar_Syntax_Syntax.fvar a1
                    FStar_Syntax_Syntax.Delta_equational None
                   in
                let uu____3861 =
                  let uu____3863 = FStar_Syntax_Syntax.as_arg phi1  in
                  let uu____3864 =
                    let uu____3866 =
                      let uu____3867 =
                        mk1
                          (FStar_Syntax_Syntax.Tm_constant
                             FStar_Const.Const_unit)
                         in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3867
                       in
                    [uu____3866]  in
                  uu____3863 :: uu____3864  in
                (uu____3860, uu____3861)  in
              FStar_Syntax_Syntax.Tm_app uu____3850  in
            mk1 uu____3849
        | FStar_Parser_AST.App
            (uu____3869,uu____3870,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3882 =
                let uu____3883 = unparen e  in uu____3883.FStar_Parser_AST.tm
                 in
              match uu____3882 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____3889 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3892 ->
            let rec aux args e =
              let uu____3913 =
                let uu____3914 = unparen e  in uu____3914.FStar_Parser_AST.tm
                 in
              match uu____3913 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3924 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3924  in
                  aux (arg :: args) e1
              | uu____3931 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3942 =
              let uu____3943 =
                let uu____3948 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____3948,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3943  in
            mk1 uu____3942
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3978 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4020  ->
                        match uu____4020 with
                        | (p,def) ->
                            let uu____4034 = is_app_pattern p  in
                            if uu____4034
                            then
                              let uu____4044 =
                                destruct_app_pattern env top_level p  in
                              (uu____4044, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4073 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4073, def1)
                               | uu____4088 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4102);
                                           FStar_Parser_AST.prange =
                                             uu____4103;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4116 =
                                            let uu____4124 =
                                              let uu____4127 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4127  in
                                            (uu____4124, [], (Some t))  in
                                          (uu____4116, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4152)
                                        ->
                                        if top_level
                                        then
                                          let uu____4164 =
                                            let uu____4172 =
                                              let uu____4175 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4175  in
                                            (uu____4172, [], None)  in
                                          (uu____4164, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4199 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4209 =
                FStar_List.fold_left
                  (fun uu____4233  ->
                     fun uu____4234  ->
                       match (uu____4233, uu____4234) with
                       | ((env1,fnames,rec_bindings),((f,uu____4278,uu____4279),uu____4280))
                           ->
                           let uu____4320 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4334 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4334 with
                                  | (env2,xx) ->
                                      let uu____4345 =
                                        let uu____4347 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4347 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4345))
                             | FStar_Util.Inr l ->
                                 let uu____4352 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4352, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4320 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4209 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4425 =
                    match uu____4425 with
                    | ((uu____4437,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4463 = is_comp_type env1 t  in
                                if uu____4463
                                then
                                  ((let uu____4465 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4470 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4470))
                                       in
                                    match uu____4465 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4473 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4474 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4474))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4473
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4479 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1))
                                uu____4479 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4481 ->
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
                              let uu____4491 =
                                let uu____4492 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4492
                                  None
                                 in
                              FStar_Util.Inr uu____4491
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
                  let uu____4512 =
                    let uu____4513 =
                      let uu____4521 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4521)  in
                    FStar_Syntax_Syntax.Tm_let uu____4513  in
                  FStar_All.pipe_left mk1 uu____4512
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4548 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4548 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4569 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4569 None  in
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
                    | LocalBinder (x,uu____4577) ->
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
                              let uu____4586 =
                                let uu____4589 =
                                  let uu____4590 =
                                    let uu____4606 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____4607 =
                                      let uu____4609 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1)
                                         in
                                      [uu____4609]  in
                                    (uu____4606, uu____4607)  in
                                  FStar_Syntax_Syntax.Tm_match uu____4590  in
                                FStar_Syntax_Syntax.mk uu____4589  in
                              uu____4586 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____4624 =
                          let uu____4625 =
                            let uu____4633 =
                              let uu____4634 =
                                let uu____4635 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____4635]  in
                              FStar_Syntax_Subst.close uu____4634 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4633)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____4625  in
                        FStar_All.pipe_left mk1 uu____4624
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
            let uu____4655 = is_rec || (is_app_pattern pat)  in
            if uu____4655
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____4661 =
              let uu____4662 =
                let uu____4678 = desugar_term env t1  in
                let uu____4679 =
                  let uu____4689 =
                    let uu____4698 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____4701 = desugar_term env t2  in
                    (uu____4698, None, uu____4701)  in
                  let uu____4709 =
                    let uu____4719 =
                      let uu____4728 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____4731 = desugar_term env t3  in
                      (uu____4728, None, uu____4731)  in
                    [uu____4719]  in
                  uu____4689 :: uu____4709  in
                (uu____4678, uu____4679)  in
              FStar_Syntax_Syntax.Tm_match uu____4662  in
            mk1 uu____4661
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
            let desugar_branch uu____4817 =
              match uu____4817 with
              | (pat,wopt,b) ->
                  let uu____4827 = desugar_match_pat env pat  in
                  (match uu____4827 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4836 = desugar_term env1 e1  in
                             Some uu____4836
                          in
                       let b1 = desugar_term env1 b  in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1))
               in
            let uu____4839 =
              let uu____4840 =
                let uu____4856 = desugar_term env e  in
                let uu____4857 = FStar_List.map desugar_branch branches  in
                (uu____4856, uu____4857)  in
              FStar_Syntax_Syntax.Tm_match uu____4840  in
            FStar_All.pipe_left mk1 uu____4839
        | FStar_Parser_AST.Ascribed (e,t) ->
            let annot =
              let uu____4873 = is_comp_type env t  in
              if uu____4873
              then
                let uu____4878 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____4878
              else
                (let uu____4884 = desugar_term env t  in
                 FStar_Util.Inl uu____4884)
               in
            let uu____4887 =
              let uu____4888 =
                let uu____4901 = desugar_term env e  in
                (uu____4901, annot, None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____4888  in
            FStar_All.pipe_left mk1 uu____4887
        | FStar_Parser_AST.Record (uu____4909,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____4930 = FStar_List.hd fields  in
              match uu____4930 with | (f,uu____4937) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4961  ->
                        match uu____4961 with
                        | (g,uu____4965) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____4969,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4977 =
                         let uu____4978 =
                           let uu____4981 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____4981, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____4978  in
                       Prims.raise uu____4977
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
                  let uu____4987 =
                    let uu____4993 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5007  ->
                              match uu____5007 with
                              | (f,uu____5013) ->
                                  let uu____5014 =
                                    let uu____5015 = get_field None f  in
                                    FStar_All.pipe_left Prims.snd uu____5015
                                     in
                                  (uu____5014, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____4993)  in
                  FStar_Parser_AST.Construct uu____4987
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5026 =
                      let uu____5027 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5027  in
                    FStar_Parser_AST.mk_term uu____5026 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5029 =
                      let uu____5036 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5050  ->
                                match uu____5050 with
                                | (f,uu____5056) -> get_field (Some xterm) f))
                         in
                      (None, uu____5036)  in
                    FStar_Parser_AST.Record uu____5029  in
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
                         FStar_Syntax_Syntax.tk = uu____5072;
                         FStar_Syntax_Syntax.pos = uu____5073;
                         FStar_Syntax_Syntax.vars = uu____5074;_},args);
                    FStar_Syntax_Syntax.tk = uu____5076;
                    FStar_Syntax_Syntax.pos = uu____5077;
                    FStar_Syntax_Syntax.vars = uu____5078;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5100 =
                     let uu____5101 =
                       let uu____5111 =
                         let uu____5112 =
                           let uu____5114 =
                             let uu____5115 =
                               let uu____5119 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5119)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5115  in
                           Some uu____5114  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5112
                          in
                       (uu____5111, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5101  in
                   FStar_All.pipe_left mk1 uu____5100  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5143 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5146 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
               in
            (match uu____5146 with
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
                 let uu____5159 =
                   let uu____5160 =
                     let uu____5170 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual1
                        in
                     let uu____5171 =
                       let uu____5173 = FStar_Syntax_Syntax.as_arg e1  in
                       [uu____5173]  in
                     (uu____5170, uu____5171)  in
                   FStar_Syntax_Syntax.Tm_app uu____5160  in
                 FStar_All.pipe_left mk1 uu____5159)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5179 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5180 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5181,uu____5182,uu____5183) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5190,uu____5191,uu____5192) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5199,uu____5200,uu____5201) ->
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
           (fun uu____5225  ->
              match uu____5225 with
              | (a,imp) ->
                  let uu____5233 = desugar_term env a  in
                  arg_withimp_e imp uu____5233))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5250 =
          match uu____5250 with
          | (t1,uu____5254) ->
              let uu____5255 =
                let uu____5256 = unparen t1  in
                uu____5256.FStar_Parser_AST.tm  in
              (match uu____5255 with
               | FStar_Parser_AST.Requires uu____5257 -> true
               | uu____5261 -> false)
           in
        let is_ensures uu____5267 =
          match uu____5267 with
          | (t1,uu____5271) ->
              let uu____5272 =
                let uu____5273 = unparen t1  in
                uu____5273.FStar_Parser_AST.tm  in
              (match uu____5272 with
               | FStar_Parser_AST.Ensures uu____5274 -> true
               | uu____5278 -> false)
           in
        let is_app head1 uu____5287 =
          match uu____5287 with
          | (t1,uu____5291) ->
              let uu____5292 =
                let uu____5293 = unparen t1  in
                uu____5293.FStar_Parser_AST.tm  in
              (match uu____5292 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5295;
                      FStar_Parser_AST.level = uu____5296;_},uu____5297,uu____5298)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5299 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5317 = head_and_args t1  in
          match uu____5317 with
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
                   let uu____5482 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____5482, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5496 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5496
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5505 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5505
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
               | uu____5525 ->
                   let default_effect =
                     let uu____5527 = FStar_Options.ml_ish ()  in
                     if uu____5527
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5530 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____5530
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
        let uu____5543 = pre_process_comp_typ t  in
        match uu____5543 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5573 =
                  let uu____5574 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5574
                   in
                fail uu____5573)
             else ();
             (let is_universe uu____5581 =
                match uu____5581 with
                | (uu____5584,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____5586 = FStar_Util.take is_universe args  in
              match uu____5586 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5617  ->
                         match uu____5617 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____5622 =
                    let uu____5630 = FStar_List.hd args1  in
                    let uu____5635 = FStar_List.tl args1  in
                    (uu____5630, uu____5635)  in
                  (match uu____5622 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg)  in
                       let rest1 = desugar_args env rest  in
                       let uu____5666 =
                         FStar_All.pipe_right rest1
                           (FStar_List.partition
                              (fun uu____5704  ->
                                 match uu____5704 with
                                 | (t1,uu____5711) ->
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____5719;
                                             FStar_Syntax_Syntax.pos =
                                               uu____5720;
                                             FStar_Syntax_Syntax.vars =
                                               uu____5721;_},uu____5722::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____5744 -> false)))
                          in
                       (match uu____5666 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5787  ->
                                      match uu____5787 with
                                      | (t1,uu____5794) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5801,(arg,uu____5803)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5825 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5837 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
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
                                                 let uu____5929 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____5929
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____5941 -> pat  in
                                         let uu____5942 =
                                           let uu____5949 =
                                             let uu____5956 =
                                               let uu____5962 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____5962, aq)  in
                                             [uu____5956]  in
                                           ens :: uu____5949  in
                                         req :: uu____5942
                                     | uu____5998 -> rest2
                                   else rest2  in
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
        | uu____6014 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___219_6055 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___219_6055.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___219_6055.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___219_6055.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___220_6085 = b  in
             {
               FStar_Parser_AST.b = (uu___220_6085.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___220_6085.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___220_6085.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6118 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6118)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6127 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6127 with
             | (env1,a1) ->
                 let a2 =
                   let uu___221_6135 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___221_6135.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___221_6135.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6148 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6157 =
                     let uu____6160 =
                       let uu____6164 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6164]  in
                     no_annot_abs uu____6160 body2  in
                   FStar_All.pipe_left setpos uu____6157  in
                 let uu____6169 =
                   let uu____6170 =
                     let uu____6180 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6181 =
                       let uu____6183 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6183]  in
                     (uu____6180, uu____6181)  in
                   FStar_Syntax_Syntax.Tm_app uu____6170  in
                 FStar_All.pipe_left mk1 uu____6169)
        | uu____6187 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6236 = q (rest, pats, body)  in
              let uu____6240 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6236 uu____6240
                FStar_Parser_AST.Formula
               in
            let uu____6241 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6241 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6246 -> failwith "impossible"  in
      let uu____6248 =
        let uu____6249 = unparen f  in uu____6249.FStar_Parser_AST.tm  in
      match uu____6248 with
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
          let uu____6279 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6279
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6300 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6300
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6325 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6329 =
        FStar_List.fold_left
          (fun uu____6342  ->
             fun b  ->
               match uu____6342 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___222_6370 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___222_6370.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___222_6370.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___222_6370.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6380 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6380 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___223_6392 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___223_6392.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___223_6392.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6401 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6329 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6451 = desugar_typ env t  in ((Some x), uu____6451)
      | FStar_Parser_AST.TVariable x ->
          let uu____6454 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____6454)
      | FStar_Parser_AST.NoName t ->
          let uu____6469 = desugar_typ env t  in (None, uu____6469)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___197_6518  ->
            match uu___197_6518 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6519 -> false))
     in
  let quals2 q =
    let uu____6527 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface
       in
    if uu____6527
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          let uu____6534 =
            let uu____6541 =
              quals2
                [FStar_Syntax_Syntax.OnlyName;
                FStar_Syntax_Syntax.Discriminator d]
               in
            (disc_name, [], FStar_Syntax_Syntax.tun, uu____6541,
              (FStar_Ident.range_of_lid disc_name))
             in
          FStar_Syntax_Syntax.Sig_declare_typ uu____6534))
  
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
            let uu____6566 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6576  ->
                        match uu____6576 with
                        | (x,uu____6581) ->
                            let uu____6582 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____6582 with
                             | (field_name,uu____6587) ->
                                 let only_decl =
                                   ((let uu____6589 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6589)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6590 =
                                        let uu____6591 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____6591.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____6590)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6601 =
                                       FStar_List.filter
                                         (fun uu___198_6603  ->
                                            match uu___198_6603 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6604 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6601
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___199_6612  ->
                                             match uu___199_6612 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6613 -> false))
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
                                      let uu____6620 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____6620
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____6624 =
                                        let uu____6627 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____6627  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6624;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____6629 =
                                        let uu____6638 =
                                          let uu____6640 =
                                            let uu____6641 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____6641
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____6640]  in
                                        ((false, [lb]), p, uu____6638,
                                          quals1, [])
                                         in
                                      FStar_Syntax_Syntax.Sig_let uu____6629
                                       in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____6566 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____6681 =
  match uu____6681 with
  | (inductive_tps,se) ->
      (match se with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6689,t,uu____6691,n1,quals,uu____6694,uu____6695) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6700 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____6700 with
            | (formals,uu____6710) ->
                (match formals with
                 | [] -> []
                 | uu____6724 ->
                     let filter_records uu___200_6732 =
                       match uu___200_6732 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6734,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6741 -> None  in
                     let fv_qual =
                       let uu____6743 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____6743 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____6750 = FStar_Util.first_N n1 formals  in
                     (match uu____6750 with
                      | (uu____6762,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6776 -> [])
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
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
                    let uu____6814 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____6814
                    then
                      let uu____6816 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____6816
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____6819 =
                      let uu____6822 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____6822  in
                    let uu____6823 =
                      let uu____6826 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____6826  in
                    let uu____6829 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6819;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6823;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6829
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
          let tycon_id uu___201_6862 =
            match uu___201_6862 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6901 =
                  let uu____6902 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____6902  in
                FStar_Parser_AST.mk_term uu____6901 x.FStar_Ident.idRange
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
              | uu____6924 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____6927 =
                     let uu____6928 =
                       let uu____6932 = binder_to_term b  in
                       (out, uu____6932, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____6928  in
                   FStar_Parser_AST.mk_term uu____6927
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___202_6939 =
            match uu___202_6939 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____6968  ->
                       match uu____6968 with
                       | (x,t,uu____6975) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____6979 =
                    let uu____6980 =
                      let uu____6981 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____6981  in
                    FStar_Parser_AST.mk_term uu____6980
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____6979 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____6984 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____6996  ->
                          match uu____6996 with
                          | (x,uu____7002,uu____7003) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____6984)
            | uu____7030 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___203_7052 =
            match uu___203_7052 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7066 = typars_of_binders _env binders  in
                (match uu____7066 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7094 =
                         let uu____7095 =
                           let uu____7096 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7096  in
                         FStar_Parser_AST.mk_term uu____7095
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7094 binders  in
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
            | uu____7107 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7133 =
              FStar_List.fold_left
                (fun uu____7149  ->
                   fun uu____7150  ->
                     match (uu____7149, uu____7150) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7198 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7198 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7133 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7259 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7259
                | uu____7260 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7265 = desugar_abstract_tc quals env [] tc  in
              (match uu____7265 with
               | (uu____7272,uu____7273,se,uu____7275) ->
                   let se1 =
                     match se with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7278,typars,k,[],[],quals1,rng1) ->
                         let quals2 =
                           let uu____7289 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7289
                           then quals1
                           else
                             ((let uu____7294 =
                                 FStar_Range.string_of_range rng1  in
                               let uu____7295 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7294 uu____7295);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7299 ->
                               let uu____7300 =
                                 let uu____7303 =
                                   let uu____7304 =
                                     let uu____7312 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7312)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7304
                                    in
                                 FStar_Syntax_Syntax.mk uu____7303  in
                               uu____7300 None rng1
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, [], t, quals2, rng1)
                     | uu____7323 -> se  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7334 = typars_of_binders env binders  in
              (match uu____7334 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7354 =
                           FStar_Util.for_some
                             (fun uu___204_7355  ->
                                match uu___204_7355 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7356 -> false) quals
                            in
                         if uu____7354
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7362 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___205_7364  ->
                               match uu___205_7364 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7365 -> false))
                        in
                     if uu____7362
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let se =
                     let uu____7371 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7371
                     then
                       let uu____7373 =
                         let uu____7377 =
                           let uu____7378 = unparen t  in
                           uu____7378.FStar_Parser_AST.tm  in
                         match uu____7377 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7390 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7406)::args_rev ->
                                   let uu____7413 =
                                     let uu____7414 = unparen last_arg  in
                                     uu____7414.FStar_Parser_AST.tm  in
                                   (match uu____7413 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7429 -> ([], args))
                               | uu____7434 -> ([], args)  in
                             (match uu____7390 with
                              | (cattributes,args1) ->
                                  let uu____7455 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7455))
                         | uu____7461 -> (t, [])  in
                       match uu____7373 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let uu____7472 =
                             let uu____7482 =
                               FStar_ToSyntax_Env.qualify env id  in
                             let uu____7483 =
                               FStar_All.pipe_right quals1
                                 (FStar_List.filter
                                    (fun uu___206_7487  ->
                                       match uu___206_7487 with
                                       | FStar_Syntax_Syntax.Effect  -> false
                                       | uu____7488 -> true))
                                in
                             (uu____7482, [], typars1, c1, uu____7483,
                               (FStar_List.append cattributes
                                  (FStar_Syntax_Util.comp_flags c1)), rng)
                              in
                           FStar_Syntax_Syntax.Sig_effect_abbrev uu____7472
                     else
                       (let t1 = desugar_typ env' t  in
                        let nm = FStar_ToSyntax_Env.qualify env id  in
                        mk_typ_abbrev nm [] typars k t1 [nm] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7497)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____7510 = tycon_record_as_variant trec  in
              (match uu____7510 with
               | (t,fs) ->
                   let uu____7520 =
                     let uu____7522 =
                       let uu____7523 =
                         let uu____7528 =
                           let uu____7530 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____7530  in
                         (uu____7528, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____7523  in
                     uu____7522 :: quals  in
                   desugar_tycon env rng uu____7520 [t])
          | uu____7533::uu____7534 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____7621 = et  in
                match uu____7621 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7735 ->
                         let trec = tc  in
                         let uu____7748 = tycon_record_as_variant trec  in
                         (match uu____7748 with
                          | (t,fs) ->
                              let uu____7779 =
                                let uu____7781 =
                                  let uu____7782 =
                                    let uu____7787 =
                                      let uu____7789 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____7789  in
                                    (uu____7787, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____7782
                                   in
                                uu____7781 :: quals1  in
                              collect_tcs uu____7779 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7835 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7835 with
                          | (env2,uu____7866,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____7944 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7944 with
                          | (env2,uu____7975,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8039 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8063 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8063 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___208_8301  ->
                             match uu___208_8301 with
                             | FStar_Util.Inr
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (id,uvs,tpars,k,uu____8333,uu____8334,uu____8335,uu____8336),binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8369 =
                                     typars_of_binders env1 binders  in
                                   match uu____8369 with
                                   | (env2,tpars1) ->
                                       let uu____8386 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8386 with
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
                                 let uu____8405 =
                                   let uu____8412 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ([], uu____8412)  in
                                 [uu____8405]
                             | FStar_Util.Inl
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (tname,univs,tpars,k,mutuals1,uu____8437,tags,uu____8439),constrs,tconstr,quals1)
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
                                 let uu____8492 = push_tparams env1 tpars  in
                                 (match uu____8492 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8527  ->
                                             match uu____8527 with
                                             | (x,uu____8535) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____8540 =
                                        let uu____8551 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8591  ->
                                                  match uu____8591 with
                                                  | (id,topt,uu____8608,of_notation)
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
                                                        let uu____8620 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____8620
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
                                                                uu___207_8626
                                                                 ->
                                                                match uu___207_8626
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8633
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____8639 =
                                                        let uu____8646 =
                                                          let uu____8647 =
                                                            let uu____8658 =
                                                              let uu____8661
                                                                =
                                                                let uu____8664
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  uu____8664
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                data_tpars
                                                                uu____8661
                                                               in
                                                            (name, univs,
                                                              uu____8658,
                                                              tname, ntps,
                                                              quals2,
                                                              mutuals1, rng)
                                                             in
                                                          FStar_Syntax_Syntax.Sig_datacon
                                                            uu____8647
                                                           in
                                                        (tps, uu____8646)  in
                                                      (name, uu____8639)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8551
                                         in
                                      (match uu____8540 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             (FStar_Syntax_Syntax.Sig_inductive_typ
                                                (tname, univs, tpars, k,
                                                  mutuals1, constrNames,
                                                  tags, rng)))
                                           :: constrs1))
                             | uu____8749 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd)
                      in
                   let uu____8797 =
                     let uu____8801 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____8801 rng
                      in
                   (match uu____8797 with
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
                               (fun uu___209_8835  ->
                                  match uu___209_8835 with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____8838,tps,k,uu____8841,constrs,quals1,uu____8844)
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
                                  | uu____8858 -> []))
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
      let uu____8876 =
        FStar_List.fold_left
          (fun uu____8883  ->
             fun b  ->
               match uu____8883 with
               | (env1,binders1) ->
                   let uu____8895 = desugar_binder env1 b  in
                   (match uu____8895 with
                    | (Some a,k) ->
                        let uu____8905 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____8905 with
                         | (env2,a1) ->
                             let uu____8913 =
                               let uu____8915 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___224_8916 = a1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___224_8916.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___224_8916.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    })
                                  in
                               uu____8915 :: binders1  in
                             (env2, uu____8913))
                    | uu____8918 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____8876 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
                  Prims.list)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                let uu____8996 = desugar_binders monad_env eff_binders  in
                match uu____8996 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9009 =
                        let uu____9010 =
                          let uu____9014 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          Prims.fst uu____9014  in
                        FStar_List.length uu____9010  in
                      uu____9009 = (Prims.parse_int "1")  in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"]  in
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
                          "trivial"]
                       in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____9042,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9044,uu____9045,uu____9046),uu____9047)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9064 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9065 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9071 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9071 mandatory_members)
                        eff_decls
                       in
                    (match uu____9065 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9081 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9092  ->
                                   fun decl  ->
                                     match uu____9092 with
                                     | (env2,out) ->
                                         let uu____9104 =
                                           desugar_decl env2 decl  in
                                         (match uu____9104 with
                                          | (env3,ses) ->
                                              let uu____9112 =
                                                let uu____9114 =
                                                  FStar_List.hd ses  in
                                                uu____9114 :: out  in
                                              (env3, uu____9112))) (env1, []))
                            in
                         (match uu____9081 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions1 =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9130,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9132,uu____9133,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9134,
                                                               (def,uu____9136)::
                                                               (cps_type,uu____9138)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9139;
                                                            FStar_Parser_AST.level
                                                              = uu____9140;_}),uu____9141)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9167 =
                                              FStar_ToSyntax_Env.qualify env2
                                                name
                                               in
                                            let uu____9168 =
                                              let uu____9169 =
                                                desugar_term env2 def  in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9169
                                               in
                                            let uu____9170 =
                                              let uu____9171 =
                                                desugar_typ env2 cps_type  in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9171
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                = uu____9167;
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                = name;
                                              FStar_Syntax_Syntax.action_univs
                                                = [];
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____9168;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____9170
                                            }
                                        | FStar_Parser_AST.Tycon
                                            (uu____9172,(FStar_Parser_AST.TyconAbbrev
                                                         (name,uu____9174,uu____9175,defn),uu____9177)::[])
                                            when for_free ->
                                            let uu____9194 =
                                              FStar_ToSyntax_Env.qualify env2
                                                name
                                               in
                                            let uu____9195 =
                                              let uu____9196 =
                                                desugar_term env2 defn  in
                                              FStar_Syntax_Subst.close
                                                binders1 uu____9196
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                = uu____9194;
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                = name;
                                              FStar_Syntax_Syntax.action_univs
                                                = [];
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____9195;
                                              FStar_Syntax_Syntax.action_typ
                                                = FStar_Syntax_Syntax.tun
                                            }
                                        | uu____9197 ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____9207 =
                                  let uu____9208 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9208
                                   in
                                ([], uu____9207)  in
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
                                    let uu____9220 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____9220)  in
                                  let uu____9230 =
                                    let uu____9233 =
                                      let uu____9234 =
                                        let uu____9235 = lookup "repr"  in
                                        Prims.snd uu____9235  in
                                      let uu____9240 = lookup "return"  in
                                      let uu____9241 = lookup "bind"  in
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
                                        FStar_Syntax_Syntax.repr = uu____9234;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9240;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9241;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    (uu____9233, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    uu____9230
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___210_9244  ->
                                          match uu___210_9244 with
                                          | FStar_Syntax_Syntax.Reifiable 
                                            |FStar_Syntax_Syntax.Reflectable
                                            _ -> true
                                          | uu____9246 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____9252 =
                                     let uu____9255 =
                                       let uu____9256 = lookup "return_wp"
                                          in
                                       let uu____9257 = lookup "bind_wp"  in
                                       let uu____9258 = lookup "if_then_else"
                                          in
                                       let uu____9259 = lookup "ite_wp"  in
                                       let uu____9260 = lookup "stronger"  in
                                       let uu____9261 = lookup "close_wp"  in
                                       let uu____9262 = lookup "assert_p"  in
                                       let uu____9263 = lookup "assume_p"  in
                                       let uu____9264 = lookup "null_wp"  in
                                       let uu____9265 = lookup "trivial"  in
                                       let uu____9266 =
                                         if rr
                                         then
                                           let uu____9267 = lookup "repr"  in
                                           FStar_All.pipe_left Prims.snd
                                             uu____9267
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____9276 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____9278 =
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
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____9256;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9257;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9258;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9259;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9260;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9261;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9262;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9263;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9264;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9265;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9266;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9276;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9278;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     (uu____9255,
                                       (d.FStar_Parser_AST.drange))
                                      in
                                   FStar_Syntax_Syntax.Sig_new_effect
                                     uu____9252)
                                 in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se  in
                              let env4 =
                                FStar_All.pipe_right actions1
                                  (FStar_List.fold_left
                                     (fun env4  ->
                                        fun a  ->
                                          let uu____9285 =
                                            FStar_Syntax_Util.action_as_lb
                                              mname a
                                             in
                                          FStar_ToSyntax_Env.push_sigelt env4
                                            uu____9285) env3)
                                 in
                              let env5 =
                                let uu____9287 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____9287
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
                              (env5, [se])))

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
                let env0 = env  in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                   in
                let uu____9310 = desugar_binders env1 eff_binders  in
                match uu____9310 with
                | (env2,binders) ->
                    let uu____9321 =
                      let uu____9330 = head_and_args defn  in
                      match uu____9330 with
                      | (head1,args) ->
                          let ed =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l ->
                                FStar_ToSyntax_Env.fail_or env2
                                  (FStar_ToSyntax_Env.try_lookup_effect_defn
                                     env2) l
                            | uu____9354 ->
                                let uu____9355 =
                                  let uu____9356 =
                                    let uu____9359 =
                                      let uu____9360 =
                                        let uu____9361 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____9361 " not found"
                                         in
                                      Prims.strcat "Effect " uu____9360  in
                                    (uu____9359, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____9356  in
                                Prims.raise uu____9355
                             in
                          let uu____9362 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9378)::args_rev ->
                                let uu____9385 =
                                  let uu____9386 = unparen last_arg  in
                                  uu____9386.FStar_Parser_AST.tm  in
                                (match uu____9385 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____9401 -> ([], args))
                            | uu____9406 -> ([], args)  in
                          (match uu____9362 with
                           | (cattributes,args1) ->
                               let uu____9432 = desugar_args env2 args1  in
                               let uu____9437 =
                                 desugar_attributes env2 cattributes  in
                               (ed, uu____9432, uu____9437))
                       in
                    (match uu____9321 with
                     | (ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____9470 =
                           match uu____9470 with
                           | (uu____9477,x) ->
                               let uu____9481 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____9481 with
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
                                      let uu____9501 =
                                        let uu____9502 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____9502
                                         in
                                      ([], uu____9501))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____9506 =
                             let uu____9508 = trans_qual1 (Some mname)  in
                             FStar_List.map uu____9508 quals  in
                           let uu____9511 =
                             let uu____9512 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             Prims.snd uu____9512  in
                           let uu____9518 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____9519 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____9520 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____9521 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____9522 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____9523 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____9524 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____9525 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____9526 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____9527 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____9528 =
                             let uu____9529 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             Prims.snd uu____9529  in
                           let uu____9535 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____9536 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____9537 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____9540 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____9541 =
                                    let uu____9542 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    Prims.snd uu____9542  in
                                  let uu____9548 =
                                    let uu____9549 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    Prims.snd uu____9549  in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____9540;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____9541;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____9548
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.qualifiers = uu____9506;
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____9511;
                             FStar_Syntax_Syntax.ret_wp = uu____9518;
                             FStar_Syntax_Syntax.bind_wp = uu____9519;
                             FStar_Syntax_Syntax.if_then_else = uu____9520;
                             FStar_Syntax_Syntax.ite_wp = uu____9521;
                             FStar_Syntax_Syntax.stronger = uu____9522;
                             FStar_Syntax_Syntax.close_wp = uu____9523;
                             FStar_Syntax_Syntax.assert_p = uu____9524;
                             FStar_Syntax_Syntax.assume_p = uu____9525;
                             FStar_Syntax_Syntax.null_wp = uu____9526;
                             FStar_Syntax_Syntax.trivial = uu____9527;
                             FStar_Syntax_Syntax.repr = uu____9528;
                             FStar_Syntax_Syntax.return_repr = uu____9535;
                             FStar_Syntax_Syntax.bind_repr = uu____9536;
                             FStar_Syntax_Syntax.actions = uu____9537
                           }  in
                         let se =
                           let for_free =
                             let uu____9557 =
                               let uu____9558 =
                                 let uu____9562 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 Prims.fst uu____9562  in
                               FStar_List.length uu____9558  in
                             uu____9557 = (Prims.parse_int "1")  in
                           if for_free
                           then
                             FStar_Syntax_Syntax.Sig_new_effect_for_free
                               (ed1, (d.FStar_Parser_AST.drange))
                           else
                             FStar_Syntax_Syntax.Sig_new_effect
                               (ed1, (d.FStar_Parser_AST.drange))
                            in
                         let monad_env = env2  in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se
                            in
                         let env4 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env4  ->
                                   fun a  ->
                                     let uu____9587 =
                                       FStar_Syntax_Util.action_as_lb mname a
                                        in
                                     FStar_ToSyntax_Env.push_sigelt env4
                                       uu____9587) env3)
                            in
                         let env5 =
                           let uu____9589 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____9589
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
      | FStar_Parser_AST.Fsdoc uu____9614 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____9626 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____9626, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____9647  -> match uu____9647 with | (x,uu____9652) -> x)
              tcs
             in
          let uu____9655 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d.FStar_Parser_AST.drange uu____9655 tcs1
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
               | (p,uu____9694)::[] ->
                   let uu____9699 = is_app_pattern p  in
                   Prims.op_Negation uu____9699
               | uu____9700 -> false)
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
            let uu____9711 =
              let uu____9712 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____9712.FStar_Syntax_Syntax.n  in
            (match uu____9711 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____9718) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____9738::uu____9739 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____9741 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___211_9745  ->
                               match uu___211_9745 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____9747;
                                   FStar_Syntax_Syntax.lbunivs = uu____9748;
                                   FStar_Syntax_Syntax.lbtyp = uu____9749;
                                   FStar_Syntax_Syntax.lbeff = uu____9750;
                                   FStar_Syntax_Syntax.lbdef = uu____9751;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____9758;
                                   FStar_Syntax_Syntax.lbtyp = uu____9759;
                                   FStar_Syntax_Syntax.lbeff = uu____9760;
                                   FStar_Syntax_Syntax.lbdef = uu____9761;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____9773 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____9779  ->
                             match uu____9779 with
                             | (uu____9782,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____9773
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____9790 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____9790
                   then
                     let uu____9795 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___225_9802 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___226_9803 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___226_9803.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___226_9803.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___225_9802.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___225_9802.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___225_9802.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___225_9802.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), uu____9795)
                   else lbs  in
                 let s =
                   let uu____9811 =
                     let uu____9820 =
                       FStar_All.pipe_right fvs
                         (FStar_List.map
                            (fun fv  ->
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                        in
                     (lbs1, (d.FStar_Parser_AST.drange), uu____9820, quals2,
                       attrs1)
                      in
                   FStar_Syntax_Syntax.Sig_let uu____9811  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 (env1, [s])
             | uu____9837 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____9841 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____9852 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____9841 with
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
                       let uu___227_9868 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___227_9868.FStar_Parser_AST.prange)
                       }
                   | uu____9869 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___228_9873 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___228_9873.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___228_9873.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___228_9873.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____9892 id =
                   match uu____9892 with
                   | (env1,ses) ->
                       let main =
                         let uu____9905 =
                           let uu____9906 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____9906  in
                         FStar_Parser_AST.mk_term uu____9905
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
                       let uu____9934 = desugar_decl env1 id_decl  in
                       (match uu____9934 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____9945 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____9945 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            FStar_Syntax_Syntax.Sig_main (e, (d.FStar_Parser_AST.drange))  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let uu____9959 =
            let uu____9961 =
              let uu____9962 =
                let uu____9968 = FStar_ToSyntax_Env.qualify env id  in
                (uu____9968, f, [FStar_Syntax_Syntax.Assumption],
                  (d.FStar_Parser_AST.drange))
                 in
              FStar_Syntax_Syntax.Sig_assume uu____9962  in
            [uu____9961]  in
          (env, uu____9959)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____9975 = close_fun env t  in desugar_term env uu____9975
             in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let se =
            let uu____9981 =
              let uu____9988 = FStar_ToSyntax_Env.qualify env id  in
              let uu____9989 = FStar_List.map (trans_qual1 None) quals1  in
              (uu____9988, [], t1, uu____9989, (d.FStar_Parser_AST.drange))
               in
            FStar_Syntax_Syntax.Sig_declare_typ uu____9981  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____9997 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____9997 with
           | (t,uu____10005) ->
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
            let uu____10032 =
              let uu____10036 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10036]  in
            let uu____10037 =
              let uu____10040 =
                let uu____10041 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                Prims.fst uu____10041  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10040
               in
            FStar_Syntax_Util.arrow uu____10032 uu____10037  in
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
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____10087 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____10087 with
            | None  ->
                let uu____10089 =
                  let uu____10090 =
                    let uu____10093 =
                      let uu____10094 =
                        let uu____10095 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____10095 " not found"  in
                      Prims.strcat "Effect name " uu____10094  in
                    (uu____10093, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____10090  in
                Prims.raise uu____10089
            | Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____10099 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10121 =
                  let uu____10126 =
                    let uu____10130 = desugar_term env t  in
                    ([], uu____10130)  in
                  Some uu____10126  in
                (uu____10121, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10148 =
                  let uu____10153 =
                    let uu____10157 = desugar_term env wp  in
                    ([], uu____10157)  in
                  Some uu____10153  in
                let uu____10162 =
                  let uu____10167 =
                    let uu____10171 = desugar_term env t  in
                    ([], uu____10171)  in
                  Some uu____10167  in
                (uu____10148, uu____10162)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10185 =
                  let uu____10190 =
                    let uu____10194 = desugar_term env t  in
                    ([], uu____10194)  in
                  Some uu____10190  in
                (None, uu____10185)
             in
          (match uu____10099 with
           | (lift_wp,lift) ->
               let se =
                 FStar_Syntax_Syntax.Sig_sub_effect
                   ({
                      FStar_Syntax_Syntax.source = src;
                      FStar_Syntax_Syntax.target = dst;
                      FStar_Syntax_Syntax.lift_wp = lift_wp;
                      FStar_Syntax_Syntax.lift = lift
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
        (fun uu____10245  ->
           fun d  ->
             match uu____10245 with
             | (env1,sigelts) ->
                 let uu____10257 = desugar_decl env1 d  in
                 (match uu____10257 with
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
          | (None ,uu____10299) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10302;
               FStar_Syntax_Syntax.exports = uu____10303;
               FStar_Syntax_Syntax.is_interface = uu____10304;_},FStar_Parser_AST.Module
             (current_lid,uu____10306)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10311) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____10313 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10333 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____10333, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10343 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____10343, mname, decls, false)
           in
        match uu____10313 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10361 = desugar_decls env2 decls  in
            (match uu____10361 with
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
          let uu____10386 =
            (FStar_Options.interactive ()) &&
              (let uu____10387 =
                 let uu____10388 =
                   let uu____10389 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____10389  in
                 FStar_Util.get_file_extension uu____10388  in
               uu____10387 = "fsti")
             in
          if uu____10386
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10397,uu____10398) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m  in
        let uu____10402 = desugar_modul_common curmod env m1  in
        match uu____10402 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10412 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10424 = desugar_modul_common None env m  in
      match uu____10424 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____10435 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10435
            then
              let uu____10436 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____10436
            else ());
           (let uu____10438 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____10438, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10449 =
        FStar_List.fold_left
          (fun uu____10456  ->
             fun m  ->
               match uu____10456 with
               | (env1,mods) ->
                   let uu____10468 = desugar_modul env1 m  in
                   (match uu____10468 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____10449 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10492 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____10492 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___229_10498 = en1  in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___229_10498.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___229_10498.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___229_10498.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___229_10498.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___229_10498.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___229_10498.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___229_10498.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___229_10498.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___229_10498.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___229_10498.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___229_10498.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  