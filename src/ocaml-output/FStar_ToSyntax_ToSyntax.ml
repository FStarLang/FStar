open Prims
let trans_aqual :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___181_5  ->
    match uu___181_5 with
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___183_25  ->
    match uu___183_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
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
        |FStar_Parser_AST.Ascribed (t1,_,_)|FStar_Parser_AST.LetOpen (_,t1)
          -> is_comp_type env t1
      | uu____117 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____127 =
          let uu____129 =
            let uu____130 =
              let uu____133 = FStar_Parser_AST.compile_op n1 s  in
              (uu____133, r)  in
            FStar_Ident.mk_ident uu____130  in
          [uu____129]  in
        FStar_All.pipe_right uu____127 FStar_Ident.lid_of_ids
  
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
            let uu____157 =
              let uu____158 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None
                 in
              FStar_All.pipe_right uu____158 FStar_Syntax_Syntax.fv_to_tm  in
            Some uu____157  in
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
                let uu____165 = FStar_Options.ml_ish ()  in
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
            | uu____168 -> None  in
          let uu____169 =
            let uu____173 = compile_op_lid arity s rng  in
            FStar_ToSyntax_Env.try_lookup_lid env uu____173  in
          match uu____169 with
          | Some t -> Some (Prims.fst t)
          | uu____180 -> fallback ()
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____190 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____190
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____215 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____218 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____218 with | (env1,uu____225) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____227,term) ->
          let uu____229 = free_type_vars env term  in (env, uu____229)
      | FStar_Parser_AST.TAnnotated (id,uu____233) ->
          let uu____234 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____234 with | (env1,uu____241) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____244 = free_type_vars env t  in (env, uu____244)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____249 =
        let uu____250 = unparen t  in uu____250.FStar_Parser_AST.tm  in
      match uu____249 with
      | FStar_Parser_AST.Labeled uu____252 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____258 = FStar_ToSyntax_Env.try_lookup_id env a  in
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
            (match tacopt with | None  -> [] | Some t2 -> [t2])  in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____291,ts) ->
          FStar_List.collect
            (fun uu____301  ->
               match uu____301 with | (t1,uu____306) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____307,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____313) ->
          let uu____314 = free_type_vars env t1  in
          let uu____316 = free_type_vars env t2  in
          FStar_List.append uu____314 uu____316
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____320 = free_type_vars_b env b  in
          (match uu____320 with
           | (env1,f) ->
               let uu____329 = free_type_vars env1 t1  in
               FStar_List.append f uu____329)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____337 =
            FStar_List.fold_left
              (fun uu____344  ->
                 fun binder  ->
                   match uu____344 with
                   | (env1,free) ->
                       let uu____356 = free_type_vars_b env1 binder  in
                       (match uu____356 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____337 with
           | (env1,free) ->
               let uu____374 = free_type_vars env1 body  in
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

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____416 =
        let uu____417 = unparen t1  in uu____417.FStar_Parser_AST.tm  in
      match uu____416 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____441 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____455 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____455  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____467 =
                     let uu____468 =
                       let uu____471 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____471)  in
                     FStar_Parser_AST.TAnnotated uu____468  in
                   FStar_Parser_AST.mk_binder uu____467 x.FStar_Ident.idRange
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
        let uu____482 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____482  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____494 =
                     let uu____495 =
                       let uu____498 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____498)  in
                     FStar_Parser_AST.TAnnotated uu____495  in
                   FStar_Parser_AST.mk_binder uu____494 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____500 =
             let uu____501 = unparen t  in uu____501.FStar_Parser_AST.tm  in
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
      | uu____527 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____539) -> is_var_pattern p1
    | uu____540 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____545) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____546;
           FStar_Parser_AST.prange = uu____547;_},uu____548)
        -> true
    | uu____554 -> false
  
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
    | uu____558 -> p
  
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
            let uu____584 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____584 with
             | (name,args,uu____601) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____615);
               FStar_Parser_AST.prange = uu____616;_},args)
            when is_top_level1 ->
            let uu____622 =
              let uu____625 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____625  in
            (uu____622, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____631);
               FStar_Parser_AST.prange = uu____632;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____642 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatVar (x,uu____677) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____690 = FStar_List.map Prims.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____690
      | FStar_Parser_AST.PatAscribed (pat,uu____695) ->
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
      (fun uu____704  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____722 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____742 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___185_760  ->
    match uu___185_760 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____765 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___186_782  ->
        match uu___186_782 with
        | (None ,k) ->
            let uu____791 = FStar_Syntax_Syntax.null_binder k  in
            (uu____791, env)
        | (Some a,k) ->
            let uu____795 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____795 with
             | (env1,a1) ->
                 (((let uu___207_806 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___207_806.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___207_806.FStar_Syntax_Syntax.index);
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
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None 
let mk_ref_read tm =
  let tm' =
    let uu____869 =
      let uu____879 =
        let uu____880 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____880  in
      let uu____881 =
        let uu____887 =
          let uu____892 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____892)  in
        [uu____887]  in
      (uu____879, uu____881)  in
    FStar_Syntax_Syntax.Tm_app uu____869  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____926 =
      let uu____936 =
        let uu____937 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____937  in
      let uu____938 =
        let uu____944 =
          let uu____949 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____949)  in
        [uu____944]  in
      (uu____936, uu____938)  in
    FStar_Syntax_Syntax.Tm_app uu____926  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____997 =
      let uu____1007 =
        let uu____1008 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1008  in
      let uu____1009 =
        let uu____1015 =
          let uu____1020 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1020)  in
        let uu____1023 =
          let uu____1029 =
            let uu____1034 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1034)  in
          [uu____1029]  in
        uu____1015 :: uu____1023  in
      (uu____1007, uu____1009)  in
    FStar_Syntax_Syntax.Tm_app uu____997  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___187_1060  ->
    match uu___187_1060 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1061 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1069 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1069)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1080 =
      let uu____1081 = unparen t  in uu____1081.FStar_Parser_AST.tm  in
    match uu____1080 with
    | FStar_Parser_AST.Wild  ->
        let uu____1084 =
          let uu____1085 = FStar_Unionfind.fresh None  in
          FStar_Syntax_Syntax.U_unif uu____1085  in
        FStar_Util.Inr uu____1084
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1091)) ->
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
             let uu____1134 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1134
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1141 =
               let uu____1142 =
                 let uu____1145 =
                   let uu____1146 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1146
                    in
                 (uu____1145, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1142  in
             Prims.raise uu____1141)
    | FStar_Parser_AST.App uu____1149 ->
        let rec aux t1 univargs =
          let uu____1168 =
            let uu____1169 = unparen t1  in uu____1169.FStar_Parser_AST.tm
             in
          match uu____1168 with
          | FStar_Parser_AST.App (t2,targ,uu____1174) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___188_1186  ->
                     match uu___188_1186 with
                     | FStar_Util.Inr uu____1189 -> true
                     | uu____1190 -> false) univargs
              then
                let uu____1193 =
                  let uu____1194 =
                    FStar_List.map
                      (fun uu___189_1198  ->
                         match uu___189_1198 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1194  in
                FStar_Util.Inr uu____1193
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___190_1208  ->
                        match uu___190_1208 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1212 -> failwith "impossible")
                     univargs
                    in
                 let uu____1213 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1213)
          | uu____1217 ->
              let uu____1218 =
                let uu____1219 =
                  let uu____1222 =
                    let uu____1223 =
                      let uu____1224 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1224 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1223  in
                  (uu____1222, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1219  in
              Prims.raise uu____1218
           in
        aux t []
    | uu____1229 ->
        let uu____1230 =
          let uu____1231 =
            let uu____1234 =
              let uu____1235 =
                let uu____1236 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1236 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1235  in
            (uu____1234, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1231  in
        Prims.raise uu____1230
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1270 = FStar_List.hd fields  in
  match uu____1270 with
  | (f,uu____1276) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
         in
      let check_field uu____1283 =
        match uu____1283 with
        | (f',uu____1287) ->
            let uu____1288 =
              FStar_ToSyntax_Env.belongs_to_record env f' record  in
            if uu____1288
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
      ((let uu____1292 = FStar_List.tl fields  in
        FStar_List.iter check_field uu____1292);
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1452,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1474  ->
                          match uu____1474 with
                          | (p3,uu____1480) ->
                              let uu____1481 = pat_vars p3  in
                              FStar_Util.set_union out uu____1481)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1  in
                let uu____1495 =
                  let uu____1496 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3  in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1
                     in
                  Prims.op_Negation uu____1496  in
                if uu____1495
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
         | (true ,uu____1503) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1531 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1531 with
           | Some y -> (l, e, y)
           | uu____1539 ->
               let uu____1541 = push_bv_maybe_mut e x  in
               (match uu____1541 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
               let uu____1590 =
                 let uu____1591 =
                   let uu____1592 =
                     let uu____1596 =
                       let uu____1597 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op
                          in
                       FStar_Ident.id_of_text uu____1597  in
                     (uu____1596, None)  in
                   FStar_Parser_AST.PatVar uu____1592  in
                 {
                   FStar_Parser_AST.pat = uu____1591;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1590
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1609 = aux loc env1 p2  in
               (match uu____1609 with
                | (loc1,env2,var,p3,uu____1628) ->
                    let uu____1633 =
                      FStar_List.fold_left
                        (fun uu____1646  ->
                           fun p4  ->
                             match uu____1646 with
                             | (loc2,env3,ps1) ->
                                 let uu____1669 = aux loc2 env3 p4  in
                                 (match uu____1669 with
                                  | (loc3,env4,uu____1685,p5,uu____1687) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____1633 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1)))
                            in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1731 = aux loc env1 p2  in
               (match uu____1731 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1756 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1762 = close_fun env1 t  in
                            desugar_term env1 uu____1762  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1764 -> true)
                           then
                             (let uu____1765 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1766 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1767 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1765 uu____1766 uu____1767)
                           else ();
                           LocalBinder
                             (((let uu___208_1769 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___208_1769.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___208_1769.FStar_Syntax_Syntax.index);
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
               let uu____1773 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1773, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1783 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1783, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1801 = resolvex loc env1 x  in
               (match uu____1801 with
                | (loc1,env2,xbv) ->
                    let uu____1815 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1815, imp))
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
               let uu____1826 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1826, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1844;_},args)
               ->
               let uu____1848 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1866  ->
                        match uu____1866 with
                        | (loc1,env2,args1) ->
                            let uu____1896 = aux loc1 env2 arg  in
                            (match uu____1896 with
                             | (loc2,env3,uu____1914,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1848 with
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
                    let uu____1963 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____1963, false))
           | FStar_Parser_AST.PatApp uu____1976 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1989 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2003  ->
                        match uu____2003 with
                        | (loc1,env2,pats1) ->
                            let uu____2025 = aux loc1 env2 pat  in
                            (match uu____2025 with
                             | (loc2,env3,uu____2041,pat1,uu____2043) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____1989 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2077 =
                        let uu____2080 =
                          let uu____2085 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2085  in
                        let uu____2086 =
                          let uu____2087 =
                            let uu____2095 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2095, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2087  in
                        FStar_All.pipe_left uu____2080 uu____2086  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2118 =
                               let uu____2119 =
                                 let uu____2127 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2127, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2119  in
                             FStar_All.pipe_left (pos_r r) uu____2118) pats1
                        uu____2077
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2159 =
                 FStar_List.fold_left
                   (fun uu____2176  ->
                      fun p2  ->
                        match uu____2176 with
                        | (loc1,env2,pats) ->
                            let uu____2207 = aux loc1 env2 p2  in
                            (match uu____2207 with
                             | (loc2,env3,uu____2225,pat,uu____2227) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2159 with
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
                    let uu____2298 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2298 with
                     | (constr,uu____2311) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2314 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2316 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2316,
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
                      (fun uu____2357  ->
                         match uu____2357 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2372  ->
                         match uu____2372 with
                         | (f,uu____2376) ->
                             let uu____2377 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2389  ->
                                       match uu____2389 with
                                       | (g,uu____2393) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2377 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2396,p2) -> p2)))
                  in
               let app =
                 let uu____2401 =
                   let uu____2402 =
                     let uu____2406 =
                       let uu____2407 =
                         let uu____2408 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2408  in
                       FStar_Parser_AST.mk_pattern uu____2407
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2406, args)  in
                   FStar_Parser_AST.PatApp uu____2402  in
                 FStar_Parser_AST.mk_pattern uu____2401
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2410 = aux loc env1 app  in
               (match uu____2410 with
                | (env2,e,b,p2,uu____2429) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2451 =
                            let uu____2452 =
                              let uu____2460 =
                                let uu___209_2461 = fv  in
                                let uu____2462 =
                                  let uu____2464 =
                                    let uu____2465 =
                                      let uu____2469 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2469)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2465
                                     in
                                  Some uu____2464  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___209_2461.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___209_2461.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2462
                                }  in
                              (uu____2460, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2452  in
                          FStar_All.pipe_left pos uu____2451
                      | uu____2488 -> p2  in
                    (env2, e, b, p3, false))
            in
         let uu____2491 = aux [] env p  in
         match uu____2491 with
         | (uu____2502,env1,b,p1,uu____2506) ->
             ((let uu____2512 = check_linear_pattern_variables p1  in
               FStar_All.pipe_left Prims.ignore uu____2512);
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
            let uu____2531 =
              let uu____2532 =
                let uu____2535 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2535, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2532  in
            (env, uu____2531, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2546 =
                  let uu____2547 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x  in
                  FStar_Ident.id_of_text uu____2547  in
                mklet uu____2546
            | FStar_Parser_AST.PatVar (x,uu____2549) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2553);
                   FStar_Parser_AST.prange = uu____2554;_},t)
                ->
                let uu____2558 =
                  let uu____2559 =
                    let uu____2562 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2563 = desugar_term env t  in
                    (uu____2562, uu____2563)  in
                  LetBinder uu____2559  in
                (env, uu____2558, None)
            | uu____2565 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2571 = desugar_data_pat env p is_mut  in
             match uu____2571 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2587 -> Some p1  in
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
  fun uu____2591  ->
    fun env  ->
      fun pat  ->
        let uu____2594 = desugar_data_pat env pat false  in
        match uu____2594 with | (env1,uu____2601,pat1) -> (env1, pat1)

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
        let uu___210_2608 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___210_2608.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___210_2608.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___210_2608.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___210_2608.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___210_2608.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___210_2608.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___210_2608.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___210_2608.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___210_2608.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___210_2608.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___210_2608.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false;
          FStar_ToSyntax_Env.docs = (uu___210_2608.FStar_ToSyntax_Env.docs)
        }  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___211_2612 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2612.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2612.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2612.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2612.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2612.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2612.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2612.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2612.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2612.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2612.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2612.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true;
          FStar_ToSyntax_Env.docs = (uu___211_2612.FStar_ToSyntax_Env.docs)
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
      fun uu____2615  ->
        fun range  ->
          match uu____2615 with
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
                let uu____2626 = FStar_ToSyntax_Env.try_lookup_lid env lid1
                   in
                match uu____2626 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2637 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1)
                       in
                    failwith uu____2637
                 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              let uu____2654 =
                let uu____2657 =
                  let uu____2658 =
                    let uu____2668 =
                      let uu____2674 =
                        let uu____2679 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____2679)  in
                      [uu____2674]  in
                    (lid2, uu____2668)  in
                  FStar_Syntax_Syntax.Tm_app uu____2658  in
                FStar_Syntax_Syntax.mk uu____2657  in
              uu____2654 None range

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
            let uu____2714 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____2714 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____2732 =
                    let uu____2733 =
                      let uu____2738 = mk_ref_read tm1  in
                      (uu____2738,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____2733  in
                  FStar_All.pipe_left mk1 uu____2732
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2752 =
          let uu____2753 = unparen t  in uu____2753.FStar_Parser_AST.tm  in
        match uu____2752 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2754; FStar_Ident.ident = uu____2755;
              FStar_Ident.nsstr = uu____2756; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2758 ->
            let uu____2759 =
              let uu____2760 =
                let uu____2763 =
                  let uu____2764 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____2764  in
                (uu____2763, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____2760  in
            Prims.raise uu____2759
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
          let uu___212_2792 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___212_2792.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___212_2792.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___212_2792.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2799 =
          let uu____2800 = unparen top  in uu____2800.FStar_Parser_AST.tm  in
        match uu____2799 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2801 -> desugar_formula env top
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
        | FStar_Parser_AST.Op ("*",uu____2830::uu____2831::[]) when
            let uu____2833 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*"
               in
            FStar_All.pipe_right uu____2833 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2845 = flatten1 t1  in
                  FStar_List.append uu____2845 [t2]
              | uu____2847 -> [t]  in
            let targs =
              let uu____2850 =
                let uu____2852 = unparen top  in flatten1 uu____2852  in
              FStar_All.pipe_right uu____2850
                (FStar_List.map
                   (fun t  ->
                      let uu____2856 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____2856))
               in
            let uu____2857 =
              let uu____2860 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2860
               in
            (match uu____2857 with
             | (tup,uu____2867) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2870 =
              let uu____2873 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              Prims.fst uu____2873  in
            FStar_All.pipe_left setpos uu____2870
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2887 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2887 with
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
                             let uu____2909 = desugar_term env t  in
                             (uu____2909, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2916; FStar_Ident.ident = uu____2917;
              FStar_Ident.nsstr = uu____2918; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2920; FStar_Ident.ident = uu____2921;
              FStar_Ident.nsstr = uu____2922; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2924; FStar_Ident.ident = uu____2925;
               FStar_Ident.nsstr = uu____2926; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2936 =
              let uu____2937 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____2937  in
            mk1 uu____2936
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2938; FStar_Ident.ident = uu____2939;
              FStar_Ident.nsstr = uu____2940; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2942; FStar_Ident.ident = uu____2943;
              FStar_Ident.nsstr = uu____2944; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2946; FStar_Ident.ident = uu____2947;
              FStar_Ident.nsstr = uu____2948; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2952;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2953 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
            (match uu____2953 with
             | Some ed ->
                 let uu____2956 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2956
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  ->
                 let uu____2957 =
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     (FStar_Ident.text_of_lid eff_name) txt
                    in
                 failwith uu____2957)
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____2961 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2961 with
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
              let uu____2977 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____2977 with
              | Some uu____2982 -> Some (true, l)
              | None  ->
                  let uu____2985 =
                    FStar_ToSyntax_Env.try_lookup_root_effect_name env l  in
                  (match uu____2985 with
                   | Some new_name -> Some (false, new_name)
                   | uu____2993 -> None)
               in
            (match name with
             | Some (resolve,new_name) ->
                 let uu____3001 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     new_name i
                    in
                 desugar_name mk1 setpos env resolve uu____3001
             | uu____3002 ->
                 let uu____3006 =
                   let uu____3007 =
                     let uu____3010 =
                       FStar_Util.format1
                         "Data constructor or effect %s not found"
                         l.FStar_Ident.str
                        in
                     (uu____3010, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____3007  in
                 Prims.raise uu____3006)
        | FStar_Parser_AST.Discrim lid ->
            let uu____3012 = FStar_ToSyntax_Env.try_lookup_datacon env lid
               in
            (match uu____3012 with
             | None  ->
                 let uu____3014 =
                   let uu____3015 =
                     let uu____3018 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str
                        in
                     (uu____3018, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____3015  in
                 Prims.raise uu____3014
             | uu____3019 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 desugar_name mk1 setpos env true lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3030 = FStar_ToSyntax_Env.try_lookup_datacon env l  in
            (match uu____3030 with
             | Some head1 ->
                 let uu____3033 =
                   let uu____3038 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                      in
                   (uu____3038, true)  in
                 (match uu____3033 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3051 ->
                           let uu____3055 =
                             FStar_Util.take
                               (fun uu____3066  ->
                                  match uu____3066 with
                                  | (uu____3069,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args
                              in
                           (match uu____3055 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes
                                   in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3102  ->
                                       match uu____3102 with
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
                 let error_msg =
                   let uu____3134 =
                     FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                   match uu____3134 with
                   | None  ->
                       Prims.strcat "Constructor "
                         (Prims.strcat l.FStar_Ident.str " not found")
                   | Some uu____3136 ->
                       Prims.strcat "Effect "
                         (Prims.strcat l.FStar_Ident.str
                            " used at an unexpected position")
                    in
                 Prims.raise
                   (FStar_Errors.Error
                      (error_msg, (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3141 =
              FStar_List.fold_left
                (fun uu____3158  ->
                   fun b  ->
                     match uu____3158 with
                     | (env1,tparams,typs) ->
                         let uu____3189 = desugar_binder env1 b  in
                         (match uu____3189 with
                          | (xopt,t1) ->
                              let uu____3205 =
                                match xopt with
                                | None  ->
                                    let uu____3210 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3210)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3205 with
                               | (env2,x) ->
                                   let uu____3222 =
                                     let uu____3224 =
                                       let uu____3226 =
                                         let uu____3227 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3227
                                          in
                                       [uu____3226]  in
                                     FStar_List.append typs uu____3224  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___213_3240 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___213_3240.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___213_3240.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3222))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3141 with
             | (env1,uu____3253,targs) ->
                 let uu____3265 =
                   let uu____3268 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3268
                    in
                 (match uu____3265 with
                  | (tup,uu____3275) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3283 = uncurry binders t  in
            (match uu____3283 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___191_3306 =
                   match uu___191_3306 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3316 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3316
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3332 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3332 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3343 = desugar_binder env b  in
            (match uu____3343 with
             | (None ,uu____3347) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3353 = as_binder env None b1  in
                 (match uu____3353 with
                  | ((x,uu____3357),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3362 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3362))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3377 =
              FStar_List.fold_left
                (fun uu____3384  ->
                   fun pat  ->
                     match uu____3384 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3399,t) ->
                              let uu____3401 =
                                let uu____3403 = free_type_vars env1 t  in
                                FStar_List.append uu____3403 ftvs  in
                              (env1, uu____3401)
                          | uu____3406 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3377 with
             | (uu____3409,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3417 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3417 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___192_3446 =
                   match uu___192_3446 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3475 =
                                 let uu____3476 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3476
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3475 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3518 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3518
                   | p::rest ->
                       let uu____3526 = desugar_binding_pat env1 p  in
                       (match uu____3526 with
                        | (env2,b,pat) ->
                            let uu____3538 =
                              match b with
                              | LetBinder uu____3557 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3588) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3611 =
                                          let uu____3614 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____3614, p1)  in
                                        Some uu____3611
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3639,uu____3640) ->
                                             let tup2 =
                                               let uu____3642 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3642
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3646 =
                                                 let uu____3649 =
                                                   let uu____3650 =
                                                     let uu____3660 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____3663 =
                                                       let uu____3665 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____3666 =
                                                         let uu____3668 =
                                                           let uu____3669 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3669
                                                            in
                                                         [uu____3668]  in
                                                       uu____3665 ::
                                                         uu____3666
                                                        in
                                                     (uu____3660, uu____3663)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3650
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3649
                                                  in
                                               uu____3646 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____3684 =
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
                                                 uu____3684
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3704,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3706,pats)) ->
                                             let tupn =
                                               let uu____3733 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3733
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3743 =
                                                 let uu____3744 =
                                                   let uu____3754 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____3757 =
                                                     let uu____3763 =
                                                       let uu____3769 =
                                                         let uu____3770 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3770
                                                          in
                                                       [uu____3769]  in
                                                     FStar_List.append args
                                                       uu____3763
                                                      in
                                                   (uu____3754, uu____3757)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3744
                                                  in
                                               mk1 uu____3743  in
                                             let p2 =
                                               let uu____3785 =
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
                                                 uu____3785
                                                in
                                             Some (sc1, p2)
                                         | uu____3809 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3538 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____3850,uu____3851,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3863 =
                let uu____3864 = unparen e  in uu____3864.FStar_Parser_AST.tm
                 in
              match uu____3863 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____3870 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3873 ->
            let rec aux args e =
              let uu____3894 =
                let uu____3895 = unparen e  in uu____3895.FStar_Parser_AST.tm
                 in
              match uu____3894 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3905 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3905  in
                  aux (arg :: args) e1
              | uu____3912 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3923 =
              let uu____3924 =
                let uu____3929 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____3929,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3924  in
            mk1 uu____3923
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3959 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4001  ->
                        match uu____4001 with
                        | (p,def) ->
                            let uu____4015 = is_app_pattern p  in
                            if uu____4015
                            then
                              let uu____4025 =
                                destruct_app_pattern env top_level p  in
                              (uu____4025, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4054 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4054, def1)
                               | uu____4069 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4083);
                                           FStar_Parser_AST.prange =
                                             uu____4084;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4097 =
                                            let uu____4105 =
                                              let uu____4108 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4108  in
                                            (uu____4105, [], (Some t))  in
                                          (uu____4097, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4133)
                                        ->
                                        if top_level
                                        then
                                          let uu____4145 =
                                            let uu____4153 =
                                              let uu____4156 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4156  in
                                            (uu____4153, [], None)  in
                                          (uu____4145, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4180 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4190 =
                FStar_List.fold_left
                  (fun uu____4214  ->
                     fun uu____4215  ->
                       match (uu____4214, uu____4215) with
                       | ((env1,fnames,rec_bindings),((f,uu____4259,uu____4260),uu____4261))
                           ->
                           let uu____4301 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4315 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4315 with
                                  | (env2,xx) ->
                                      let uu____4326 =
                                        let uu____4328 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4328 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4326))
                             | FStar_Util.Inr l ->
                                 let uu____4333 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4333, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4301 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4190 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4406 =
                    match uu____4406 with
                    | ((uu____4418,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4444 = is_comp_type env1 t  in
                                if uu____4444
                                then
                                  ((let uu____4446 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4451 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4451))
                                       in
                                    match uu____4446 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4454 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4455 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4455))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4454
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4460 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4460 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4463 ->
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
                              let uu____4473 =
                                let uu____4474 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4474
                                  None
                                 in
                              FStar_Util.Inr uu____4473
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
                  let uu____4494 =
                    let uu____4495 =
                      let uu____4503 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4503)  in
                    FStar_Syntax_Syntax.Tm_let uu____4495  in
                  FStar_All.pipe_left mk1 uu____4494
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4530 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4530 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4551 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4551 None  in
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
                    | LocalBinder (x,uu____4559) ->
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
                              let uu____4568 =
                                let uu____4571 =
                                  let uu____4572 =
                                    let uu____4588 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____4589 =
                                      let uu____4591 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1)
                                         in
                                      [uu____4591]  in
                                    (uu____4588, uu____4589)  in
                                  FStar_Syntax_Syntax.Tm_match uu____4572  in
                                FStar_Syntax_Syntax.mk uu____4571  in
                              uu____4568 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____4606 =
                          let uu____4607 =
                            let uu____4615 =
                              let uu____4616 =
                                let uu____4617 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____4617]  in
                              FStar_Syntax_Subst.close uu____4616 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4615)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____4607  in
                        FStar_All.pipe_left mk1 uu____4606
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
            let uu____4637 = is_rec || (is_app_pattern pat)  in
            if uu____4637
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____4643 =
              let uu____4644 =
                let uu____4660 = desugar_term env t1  in
                let uu____4661 =
                  let uu____4671 =
                    let uu____4680 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____4683 = desugar_term env t2  in
                    (uu____4680, None, uu____4683)  in
                  let uu____4691 =
                    let uu____4701 =
                      let uu____4710 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____4713 = desugar_term env t3  in
                      (uu____4710, None, uu____4713)  in
                    [uu____4701]  in
                  uu____4671 :: uu____4691  in
                (uu____4660, uu____4661)  in
              FStar_Syntax_Syntax.Tm_match uu____4644  in
            mk1 uu____4643
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
            let desugar_branch uu____4799 =
              match uu____4799 with
              | (pat,wopt,b) ->
                  let uu____4809 = desugar_match_pat env pat  in
                  (match uu____4809 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4818 = desugar_term env1 e1  in
                             Some uu____4818
                          in
                       let b1 = desugar_term env1 b  in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1))
               in
            let uu____4821 =
              let uu____4822 =
                let uu____4838 = desugar_term env e  in
                let uu____4839 = FStar_List.map desugar_branch branches  in
                (uu____4838, uu____4839)  in
              FStar_Syntax_Syntax.Tm_match uu____4822  in
            FStar_All.pipe_left mk1 uu____4821
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____4858 = is_comp_type env t  in
              if uu____4858
              then
                let uu____4863 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____4863
              else
                (let uu____4869 = desugar_term env t  in
                 FStar_Util.Inl uu____4869)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____4874 =
              let uu____4875 =
                let uu____4893 = desugar_term env e  in
                (uu____4893, (annot, tac_opt1), None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____4875  in
            FStar_All.pipe_left mk1 uu____4874
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
        let is_smt_pat uu____5305 =
          match uu____5305 with
          | (t1,uu____5309) ->
              let uu____5310 =
                let uu____5311 = unparen t1  in
                uu____5311.FStar_Parser_AST.tm  in
              (match uu____5310 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5314);
                             FStar_Parser_AST.range = uu____5315;
                             FStar_Parser_AST.level = uu____5316;_},uu____5317)::uu____5318::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5337 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5355 = head_and_args t1  in
          match uu____5355 with
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
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Syntax_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula), None)
                        in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5572 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____5572, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5586 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5586
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5595 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5595
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
               | uu____5615 ->
                   let default_effect =
                     let uu____5617 = FStar_Options.ml_ish ()  in
                     if uu____5617
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5620 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____5620
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
        let uu____5633 = pre_process_comp_typ t  in
        match uu____5633 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5663 =
                  let uu____5664 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5664
                   in
                fail uu____5663)
             else ();
             (let is_universe uu____5671 =
                match uu____5671 with
                | (uu____5674,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____5676 = FStar_Util.take is_universe args  in
              match uu____5676 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5707  ->
                         match uu____5707 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____5712 =
                    let uu____5720 = FStar_List.hd args1  in
                    let uu____5725 = FStar_List.tl args1  in
                    (uu____5720, uu____5725)  in
                  (match uu____5712 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg)  in
                       let rest1 = desugar_args env rest  in
                       let uu____5756 =
                         let is_decrease uu____5779 =
                           match uu____5779 with
                           | (t1,uu____5786) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____5794;
                                       FStar_Syntax_Syntax.pos = uu____5795;
                                       FStar_Syntax_Syntax.vars = uu____5796;_},uu____5797::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____5819 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____5756 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5885  ->
                                      match uu____5885 with
                                      | (t1,uu____5892) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5899,(arg,uu____5901)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5923 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5935 -> false  in
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
                                                 let uu____6027 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6027
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6039 -> pat  in
                                         let uu____6040 =
                                           let uu____6047 =
                                             let uu____6054 =
                                               let uu____6060 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____6060, aq)  in
                                             [uu____6054]  in
                                           ens :: uu____6047  in
                                         req :: uu____6040
                                     | uu____6096 -> rest2
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
        | uu____6112 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___214_6153 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___214_6153.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___214_6153.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___214_6153.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___215_6183 = b  in
             {
               FStar_Parser_AST.b = (uu___215_6183.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___215_6183.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___215_6183.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6216 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6216)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6225 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6225 with
             | (env1,a1) ->
                 let a2 =
                   let uu___216_6233 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___216_6233.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___216_6233.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6246 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6255 =
                     let uu____6258 =
                       let uu____6259 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6259]  in
                     no_annot_abs uu____6258 body2  in
                   FStar_All.pipe_left setpos uu____6255  in
                 let uu____6264 =
                   let uu____6265 =
                     let uu____6275 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6276 =
                       let uu____6278 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6278]  in
                     (uu____6275, uu____6276)  in
                   FStar_Syntax_Syntax.Tm_app uu____6265  in
                 FStar_All.pipe_left mk1 uu____6264)
        | uu____6282 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6331 = q (rest, pats, body)  in
              let uu____6335 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6331 uu____6335
                FStar_Parser_AST.Formula
               in
            let uu____6336 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6336 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6341 -> failwith "impossible"  in
      let uu____6343 =
        let uu____6344 = unparen f  in uu____6344.FStar_Parser_AST.tm  in
      match uu____6343 with
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
          let uu____6374 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6374
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6395 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6395
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6420 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6424 =
        FStar_List.fold_left
          (fun uu____6437  ->
             fun b  ->
               match uu____6437 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___217_6465 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___217_6465.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___217_6465.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___217_6465.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6475 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6475 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___218_6487 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___218_6487.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___218_6487.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6496 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6424 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6546 = desugar_typ env t  in ((Some x), uu____6546)
      | FStar_Parser_AST.TVariable x ->
          let uu____6549 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____6549)
      | FStar_Parser_AST.NoName t ->
          let uu____6564 = desugar_typ env t  in (None, uu____6564)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___193_6613  ->
            match uu___193_6613 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6614 -> false))
     in
  let quals2 q =
    let uu____6622 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface
       in
    if uu____6622
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          let uu____6629 =
            let uu____6630 =
              let uu____6636 =
                quals2
                  [FStar_Syntax_Syntax.OnlyName;
                  FStar_Syntax_Syntax.Discriminator d]
                 in
              (disc_name, [], FStar_Syntax_Syntax.tun, uu____6636)  in
            FStar_Syntax_Syntax.Sig_declare_typ uu____6630  in
          {
            FStar_Syntax_Syntax.sigel = uu____6629;
            FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)
          }))
  
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
            let uu____6661 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6671  ->
                        match uu____6671 with
                        | (x,uu____6676) ->
                            let uu____6677 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____6677 with
                             | (field_name,uu____6682) ->
                                 let only_decl =
                                   ((let uu____6684 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6684)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6685 =
                                        let uu____6686 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____6686.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____6685)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6696 =
                                       FStar_List.filter
                                         (fun uu___194_6698  ->
                                            match uu___194_6698 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6699 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6696
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___195_6707  ->
                                             match uu___195_6707 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6708 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun, quals1));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name)
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6715 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____6715
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____6719 =
                                        let uu____6722 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____6722  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6719;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____6724 =
                                        let uu____6725 =
                                          let uu____6733 =
                                            let uu____6735 =
                                              let uu____6736 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right uu____6736
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____6735]  in
                                          ((false, [lb]), uu____6733, quals1,
                                            [])
                                           in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6725
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6724;
                                        FStar_Syntax_Syntax.sigrng = p
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____6661 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____6776 =
  match uu____6776 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6784,t,uu____6786,n1,quals,uu____6789) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6794 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____6794 with
            | (formals,uu____6804) ->
                (match formals with
                 | [] -> []
                 | uu____6818 ->
                     let filter_records uu___196_6826 =
                       match uu___196_6826 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6828,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6835 -> None  in
                     let fv_qual =
                       let uu____6837 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____6837 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____6844 = FStar_Util.first_N n1 formals  in
                     (match uu____6844 with
                      | (uu____6856,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6870 -> [])
  
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
                    let uu____6908 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____6908
                    then
                      let uu____6910 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____6910
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____6913 =
                      let uu____6916 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____6916  in
                    let uu____6917 =
                      let uu____6920 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____6920  in
                    let uu____6923 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6913;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6917;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6923
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let
                         ((false, [lb]), lids, quals, []));
                    FStar_Syntax_Syntax.sigrng = rng
                  }
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___197_6957 =
            match uu___197_6957 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6996 =
                  let uu____6997 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____6997  in
                FStar_Parser_AST.mk_term uu____6996 x.FStar_Ident.idRange
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
              | uu____7019 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7022 =
                     let uu____7023 =
                       let uu____7027 = binder_to_term b  in
                       (out, uu____7027, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____7023  in
                   FStar_Parser_AST.mk_term uu____7022
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___198_7034 =
            match uu___198_7034 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____7063  ->
                       match uu____7063 with
                       | (x,t,uu____7070) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____7074 =
                    let uu____7075 =
                      let uu____7076 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____7076  in
                    FStar_Parser_AST.mk_term uu____7075
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____7074 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____7079 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7091  ->
                          match uu____7091 with
                          | (x,uu____7097,uu____7098) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7079)
            | uu____7125 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___199_7147 =
            match uu___199_7147 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7161 = typars_of_binders _env binders  in
                (match uu____7161 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7189 =
                         let uu____7190 =
                           let uu____7191 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7191  in
                         FStar_Parser_AST.mk_term uu____7190
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7189 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, [], quals1));
                         FStar_Syntax_Syntax.sigrng = rng
                       }  in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____7202 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7228 =
              FStar_List.fold_left
                (fun uu____7244  ->
                   fun uu____7245  ->
                     match (uu____7244, uu____7245) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7293 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7293 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7228 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7354 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7354
                | uu____7355 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7360 = desugar_abstract_tc quals env [] tc  in
              (match uu____7360 with
               | (uu____7367,uu____7368,se,uu____7370) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7373,typars,k,[],[],quals1) ->
                         let quals2 =
                           let uu____7383 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7383
                           then quals1
                           else
                             ((let uu____7388 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               let uu____7389 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7388 uu____7389);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7393 ->
                               let uu____7394 =
                                 let uu____7397 =
                                   let uu____7398 =
                                     let uu____7406 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7406)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7398
                                    in
                                 FStar_Syntax_Syntax.mk uu____7397  in
                               uu____7394 None se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___219_7415 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (l, [], t, quals2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___219_7415.FStar_Syntax_Syntax.sigrng)
                         }
                     | uu____7418 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____7421 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____7421
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7431 = typars_of_binders env binders  in
              (match uu____7431 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7451 =
                           FStar_Util.for_some
                             (fun uu___200_7452  ->
                                match uu___200_7452 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7453 -> false) quals
                            in
                         if uu____7451
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7459 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___201_7461  ->
                               match uu___201_7461 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7462 -> false))
                        in
                     if uu____7459
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____7469 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7469
                     then
                       let uu____7471 =
                         let uu____7475 =
                           let uu____7476 = unparen t  in
                           uu____7476.FStar_Parser_AST.tm  in
                         match uu____7475 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7488 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7504)::args_rev ->
                                   let uu____7511 =
                                     let uu____7512 = unparen last_arg  in
                                     uu____7512.FStar_Parser_AST.tm  in
                                   (match uu____7511 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7527 -> ([], args))
                               | uu____7532 -> ([], args)  in
                             (match uu____7488 with
                              | (cattributes,args1) ->
                                  let uu____7553 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7553))
                         | uu____7559 -> (t, [])  in
                       match uu____7471 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let uu____7570 =
                             let uu____7571 =
                               let uu____7580 =
                                 FStar_All.pipe_right quals1
                                   (FStar_List.filter
                                      (fun uu___202_7584  ->
                                         match uu___202_7584 with
                                         | FStar_Syntax_Syntax.Effect  ->
                                             false
                                         | uu____7585 -> true))
                                  in
                               (qlid, [], typars1, c1, uu____7580,
                                 (FStar_List.append cattributes
                                    (FStar_Syntax_Util.comp_flags c1)))
                                in
                             FStar_Syntax_Syntax.Sig_effect_abbrev uu____7571
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____7570;
                             FStar_Syntax_Syntax.sigrng = rng
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7594)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____7607 = tycon_record_as_variant trec  in
              (match uu____7607 with
               | (t,fs) ->
                   let uu____7617 =
                     let uu____7619 =
                       let uu____7620 =
                         let uu____7625 =
                           let uu____7627 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____7627  in
                         (uu____7625, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____7620  in
                     uu____7619 :: quals  in
                   desugar_tycon env d uu____7617 [t])
          | uu____7630::uu____7631 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____7718 = et  in
                match uu____7718 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7832 ->
                         let trec = tc  in
                         let uu____7845 = tycon_record_as_variant trec  in
                         (match uu____7845 with
                          | (t,fs) ->
                              let uu____7876 =
                                let uu____7878 =
                                  let uu____7879 =
                                    let uu____7884 =
                                      let uu____7886 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____7886  in
                                    (uu____7884, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____7879
                                   in
                                uu____7878 :: quals1  in
                              collect_tcs uu____7876 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7932 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7932 with
                          | (env2,uu____7963,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8041 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8041 with
                          | (env2,uu____8072,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8136 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8160 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8160 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___204_8410  ->
                             match uu___204_8410 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8446,uu____8447,uu____8448);
                                    FStar_Syntax_Syntax.sigrng = uu____8449;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8482 =
                                     typars_of_binders env1 binders  in
                                   match uu____8482 with
                                   | (env2,tpars1) ->
                                       let uu____8499 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8499 with
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
                                 let uu____8518 =
                                   let uu____8529 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8529)
                                    in
                                 [uu____8518]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8566,tags);
                                    FStar_Syntax_Syntax.sigrng = uu____8568;_},constrs,tconstr,quals1)
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
                                 let uu____8621 = push_tparams env1 tpars  in
                                 (match uu____8621 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8660  ->
                                             match uu____8660 with
                                             | (x,uu____8668) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____8673 =
                                        let uu____8688 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8740  ->
                                                  match uu____8740 with
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
                                                           | Some t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____8773 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____8773
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
                                                                uu___203_8779
                                                                 ->
                                                                match uu___203_8779
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8786
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____8792 =
                                                        let uu____8803 =
                                                          let uu____8804 =
                                                            let uu____8805 =
                                                              let uu____8815
                                                                =
                                                                let uu____8818
                                                                  =
                                                                  let uu____8821
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____8821
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____8818
                                                                 in
                                                              (name, univs,
                                                                uu____8815,
                                                                tname, ntps,
                                                                quals2,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____8805
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____8804;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____8803)
                                                         in
                                                      (name, uu____8792)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8688
                                         in
                                      (match uu____8673 with
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
                             | uu____8946 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9011  ->
                             match uu____9011 with
                             | (name_doc,uu____9026,uu____9027) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9066  ->
                             match uu____9066 with
                             | (uu____9077,uu____9078,se) -> se))
                      in
                   let uu____9094 =
                     let uu____9098 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9098 rng
                      in
                   (match uu____9094 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9132  ->
                                  match uu____9132 with
                                  | (uu____9144,tps,se) ->
                                      mk_data_projector_names quals env3
                                        (tps, se)))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9176,tps,k,uu____9179,constrs,quals1)
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
                                  | uu____9195 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9204  ->
                                 match uu____9204 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
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
      let uu____9226 =
        FStar_List.fold_left
          (fun uu____9233  ->
             fun b  ->
               match uu____9233 with
               | (env1,binders1) ->
                   let uu____9245 = desugar_binder env1 b  in
                   (match uu____9245 with
                    | (Some a,k) ->
                        let uu____9255 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k)
                           in
                        (match uu____9255 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9265 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____9226 with
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
                let uu____9343 = desugar_binders monad_env eff_binders  in
                match uu____9343 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9356 =
                        let uu____9357 =
                          let uu____9361 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          Prims.fst uu____9361  in
                        FStar_List.length uu____9357  in
                      uu____9356 = (Prims.parse_int "1")  in
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
                          (uu____9389,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9391,uu____9392,uu____9393),uu____9394)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9411 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9412 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9418 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9418 mandatory_members)
                        eff_decls
                       in
                    (match uu____9412 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9428 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9439  ->
                                   fun decl  ->
                                     match uu____9439 with
                                     | (env2,out) ->
                                         let uu____9451 =
                                           desugar_decl env2 decl  in
                                         (match uu____9451 with
                                          | (env3,ses) ->
                                              let uu____9459 =
                                                let uu____9461 =
                                                  FStar_List.hd ses  in
                                                uu____9461 :: out  in
                                              (env3, uu____9459))) (env1, []))
                            in
                         (match uu____9428 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9489,(FStar_Parser_AST.TyconAbbrev
                                                         (name,params,uu____9492,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9493,
                                                               (def,uu____9495)::
                                                               (cps_type,uu____9497)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9498;
                                                            FStar_Parser_AST.level
                                                              = uu____9499;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9526 =
                                              desugar_binders env2 params  in
                                            (match uu____9526 with
                                             | (env3,params1) ->
                                                 let params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     params1
                                                    in
                                                 let uu____9538 =
                                                   let uu____9539 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9540 =
                                                     let uu____9541 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1 params2)
                                                       uu____9541
                                                      in
                                                   let uu____9544 =
                                                     let uu____9545 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1 params2)
                                                       uu____9545
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9539;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9540;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9544
                                                   }  in
                                                 (uu____9538, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9549,(FStar_Parser_AST.TyconAbbrev
                                                         (name,params,uu____9552,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9571 =
                                              desugar_binders env2 params  in
                                            (match uu____9571 with
                                             | (env3,params1) ->
                                                 let params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     params1
                                                    in
                                                 let uu____9583 =
                                                   let uu____9584 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9585 =
                                                     let uu____9586 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1 params2)
                                                       uu____9586
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9584;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9585;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____9583, doc1))
                                        | uu____9590 ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let actions1 =
                                FStar_List.map Prims.fst actions_docs  in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____9609 =
                                  let uu____9610 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9610
                                   in
                                ([], uu____9609)  in
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
                                    let uu____9622 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____9622)  in
                                  let uu____9632 =
                                    let uu____9633 =
                                      let uu____9634 =
                                        let uu____9635 = lookup "repr"  in
                                        Prims.snd uu____9635  in
                                      let uu____9640 = lookup "return"  in
                                      let uu____9641 = lookup "bind"  in
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
                                        FStar_Syntax_Syntax.repr = uu____9634;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9640;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9641;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9633
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9632;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange)
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___205_9644  ->
                                          match uu___205_9644 with
                                          | FStar_Syntax_Syntax.Reifiable 
                                            |FStar_Syntax_Syntax.Reflectable
                                            _ -> true
                                          | uu____9646 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____9652 =
                                     let uu____9653 =
                                       let uu____9654 = lookup "return_wp"
                                          in
                                       let uu____9655 = lookup "bind_wp"  in
                                       let uu____9656 = lookup "if_then_else"
                                          in
                                       let uu____9657 = lookup "ite_wp"  in
                                       let uu____9658 = lookup "stronger"  in
                                       let uu____9659 = lookup "close_wp"  in
                                       let uu____9660 = lookup "assert_p"  in
                                       let uu____9661 = lookup "assume_p"  in
                                       let uu____9662 = lookup "null_wp"  in
                                       let uu____9663 = lookup "trivial"  in
                                       let uu____9664 =
                                         if rr
                                         then
                                           let uu____9665 = lookup "repr"  in
                                           FStar_All.pipe_left Prims.snd
                                             uu____9665
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____9674 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____9676 =
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
                                           uu____9654;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9655;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9656;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9657;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9658;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9659;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9660;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9661;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9662;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9663;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9664;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9674;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9676;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9653
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9652;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange)
                                   })
                                 in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se  in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____9689  ->
                                          match uu____9689 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____9698 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____9698
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____9700 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____9700
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env)
                                     in
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
                                    }  in
                                  FStar_ToSyntax_Env.push_sigelt env5
                                    refl_decl
                                else env5  in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

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
                let uu____9724 = desugar_binders env1 eff_binders  in
                match uu____9724 with
                | (env2,binders) ->
                    let uu____9735 =
                      let uu____9745 = head_and_args defn  in
                      match uu____9745 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____9770 ->
                                let uu____9771 =
                                  let uu____9772 =
                                    let uu____9775 =
                                      let uu____9776 =
                                        let uu____9777 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____9777 " not found"
                                         in
                                      Prims.strcat "Effect " uu____9776  in
                                    (uu____9775, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____9772  in
                                Prims.raise uu____9771
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____9779 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9795)::args_rev ->
                                let uu____9802 =
                                  let uu____9803 = unparen last_arg  in
                                  uu____9803.FStar_Parser_AST.tm  in
                                (match uu____9802 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____9818 -> ([], args))
                            | uu____9823 -> ([], args)  in
                          (match uu____9779 with
                           | (cattributes,args1) ->
                               let uu____9850 = desugar_args env2 args1  in
                               let uu____9855 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____9850, uu____9855))
                       in
                    (match uu____9735 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____9889 =
                           match uu____9889 with
                           | (uu____9896,x) ->
                               let uu____9900 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____9900 with
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
                                      let uu____9920 =
                                        let uu____9921 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____9921
                                         in
                                      ([], uu____9920))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____9925 =
                             let uu____9927 = trans_qual1 (Some mname)  in
                             FStar_List.map uu____9927 quals  in
                           let uu____9930 =
                             let uu____9931 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             Prims.snd uu____9931  in
                           let uu____9937 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____9938 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____9939 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____9940 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____9941 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____9942 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____9943 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____9944 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____9945 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____9946 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____9947 =
                             let uu____9948 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             Prims.snd uu____9948  in
                           let uu____9954 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____9955 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____9956 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____9959 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____9960 =
                                    let uu____9961 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    Prims.snd uu____9961  in
                                  let uu____9967 =
                                    let uu____9968 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    Prims.snd uu____9968  in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____9959;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____9960;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____9967
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.qualifiers = uu____9925;
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____9930;
                             FStar_Syntax_Syntax.ret_wp = uu____9937;
                             FStar_Syntax_Syntax.bind_wp = uu____9938;
                             FStar_Syntax_Syntax.if_then_else = uu____9939;
                             FStar_Syntax_Syntax.ite_wp = uu____9940;
                             FStar_Syntax_Syntax.stronger = uu____9941;
                             FStar_Syntax_Syntax.close_wp = uu____9942;
                             FStar_Syntax_Syntax.assert_p = uu____9943;
                             FStar_Syntax_Syntax.assume_p = uu____9944;
                             FStar_Syntax_Syntax.null_wp = uu____9945;
                             FStar_Syntax_Syntax.trivial = uu____9946;
                             FStar_Syntax_Syntax.repr = uu____9947;
                             FStar_Syntax_Syntax.return_repr = uu____9954;
                             FStar_Syntax_Syntax.bind_repr = uu____9955;
                             FStar_Syntax_Syntax.actions = uu____9956
                           }  in
                         let se =
                           let for_free =
                             let uu____9976 =
                               let uu____9977 =
                                 let uu____9981 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 Prims.fst uu____9981  in
                               FStar_List.length uu____9977  in
                             uu____9976 = (Prims.parse_int "1")  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange)
                           }  in
                         let monad_env = env2  in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se
                            in
                         let env4 =
                           FStar_ToSyntax_Env.push_doc env3 ed_lid
                             d.FStar_Parser_AST.doc
                            in
                         let env5 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env5  ->
                                   fun a  ->
                                     let doc1 =
                                       FStar_ToSyntax_Env.try_lookup_doc env5
                                         a.FStar_Syntax_Syntax.action_name
                                        in
                                     let env6 =
                                       let uu____10010 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10010
                                        in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____10012 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____10012
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env)
                                in
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
                               }  in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5  in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc
                            in
                         (env7, [se]))

and desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____10038 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10050 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____10050, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____10071  ->
                 match uu____10071 with | (x,uu____10076) -> x) tcs
             in
          let uu____10079 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d uu____10079 tcs1
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
               | (p,uu____10118)::[] ->
                   let uu____10123 = is_app_pattern p  in
                   Prims.op_Negation uu____10123
               | uu____10124 -> false)
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
            let uu____10135 =
              let uu____10136 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____10136.FStar_Syntax_Syntax.n  in
            (match uu____10135 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10142) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____10162::uu____10163 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10165 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___206_10169  ->
                               match uu___206_10169 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10171;
                                   FStar_Syntax_Syntax.lbunivs = uu____10172;
                                   FStar_Syntax_Syntax.lbtyp = uu____10173;
                                   FStar_Syntax_Syntax.lbeff = uu____10174;
                                   FStar_Syntax_Syntax.lbdef = uu____10175;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10182;
                                   FStar_Syntax_Syntax.lbtyp = uu____10183;
                                   FStar_Syntax_Syntax.lbeff = uu____10184;
                                   FStar_Syntax_Syntax.lbdef = uu____10185;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____10197 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10203  ->
                             match uu____10203 with
                             | (uu____10206,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____10197
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____10214 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____10214
                   then
                     let uu____10219 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___220_10226 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___221_10227 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___221_10227.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___221_10227.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___220_10226.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___220_10226.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___220_10226.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___220_10226.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), uu____10219)
                   else lbs  in
                 let names =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let
                          (lbs1, names, quals2, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names
                    in
                 (env2, [s])
             | uu____10255 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10259 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10270 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____10259 with
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
                       let uu___222_10286 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___222_10286.FStar_Parser_AST.prange)
                       }
                   | uu____10287 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___223_10291 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___223_10291.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___223_10291.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___223_10291.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____10310 id =
                   match uu____10310 with
                   | (env1,ses) ->
                       let main =
                         let uu____10323 =
                           let uu____10324 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____10324  in
                         FStar_Parser_AST.mk_term uu____10323
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
                       let uu____10352 = desugar_decl env1 id_decl  in
                       (match uu____10352 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____10363 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____10363 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume
                    (lid, f, [FStar_Syntax_Syntax.Assumption]));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____10385 = close_fun env t  in
            desugar_term env uu____10385  in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____10392 =
              let uu____10393 =
                let uu____10399 = FStar_List.map (trans_qual1 None) quals1
                   in
                (lid, [], t1, uu____10399)  in
              FStar_Syntax_Syntax.Sig_declare_typ uu____10393  in
            {
              FStar_Syntax_Syntax.sigel = uu____10392;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10408 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____10408 with
           | (t,uu____10416) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Syntax_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Syntax_Syntax.ExceptionConstructor],
                          [FStar_Syntax_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle
                        ([se], [FStar_Syntax_Syntax.ExceptionConstructor],
                          [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 }  in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 ([], se)  in
               let discs =
                 mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l]
                  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____10444 =
              let uu____10448 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10448]  in
            let uu____10449 =
              let uu____10452 =
                let uu____10453 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                Prims.fst uu____10453  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10452
               in
            FStar_Syntax_Util.arrow uu____10444 uu____10449  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 ([], se)  in
          let discs =
            mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l]
             in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
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
            let uu____10500 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____10500 with
            | None  ->
                let uu____10502 =
                  let uu____10503 =
                    let uu____10506 =
                      let uu____10507 =
                        let uu____10508 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____10508 " not found"  in
                      Prims.strcat "Effect name " uu____10507  in
                    (uu____10506, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____10503  in
                Prims.raise uu____10502
            | Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____10512 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10534 =
                  let uu____10539 =
                    let uu____10543 = desugar_term env t  in
                    ([], uu____10543)  in
                  Some uu____10539  in
                (uu____10534, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10561 =
                  let uu____10566 =
                    let uu____10570 = desugar_term env wp  in
                    ([], uu____10570)  in
                  Some uu____10566  in
                let uu____10575 =
                  let uu____10580 =
                    let uu____10584 = desugar_term env t  in
                    ([], uu____10584)  in
                  Some uu____10580  in
                (uu____10561, uu____10575)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10598 =
                  let uu____10603 =
                    let uu____10607 = desugar_term env t  in
                    ([], uu____10607)  in
                  Some uu____10603  in
                (None, uu____10598)
             in
          (match uu____10512 with
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
                 }  in
               (env, [se]))

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10658  ->
           fun d  ->
             match uu____10658 with
             | (env1,sigelts) ->
                 let uu____10670 = desugar_decl env1 d  in
                 (match uu____10670 with
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
          | (None ,uu____10712) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10715;
               FStar_Syntax_Syntax.exports = uu____10716;
               FStar_Syntax_Syntax.is_interface = uu____10717;_},FStar_Parser_AST.Module
             (current_lid,uu____10719)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10724) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____10726 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10746 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____10746, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10756 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____10756, mname, decls, false)
           in
        match uu____10726 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10774 = desugar_decls env2 decls  in
            (match uu____10774 with
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
          let uu____10799 =
            (FStar_Options.interactive ()) &&
              (let uu____10800 =
                 let uu____10801 =
                   let uu____10802 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____10802  in
                 FStar_Util.get_file_extension uu____10801  in
               uu____10800 = "fsti")
             in
          if uu____10799
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10810,uu____10811) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m  in
        let uu____10815 = desugar_modul_common curmod env m1  in
        match uu____10815 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10825 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10837 = desugar_modul_common None env m  in
      match uu____10837 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____10848 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10848
            then
              let uu____10849 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____10849
            else ());
           (let uu____10851 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____10851, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10862 =
        FStar_List.fold_left
          (fun uu____10869  ->
             fun m  ->
               match uu____10869 with
               | (env1,mods) ->
                   let uu____10881 = desugar_modul env1 m  in
                   (match uu____10881 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____10862 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10905 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____10905 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___224_10911 = en1  in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___224_10911.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___224_10911.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___224_10911.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___224_10911.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___224_10911.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___224_10911.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___224_10911.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___224_10911.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___224_10911.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___224_10911.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___224_10911.FStar_ToSyntax_Env.expect_typ);
                 FStar_ToSyntax_Env.docs =
                   (uu___224_10911.FStar_ToSyntax_Env.docs)
               }) m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  