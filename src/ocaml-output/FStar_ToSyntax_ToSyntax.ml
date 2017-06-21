open Prims
let desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.branch Prims.list
  =
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
let trans_aqual :
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___198_51  ->
    match uu___198_51 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____54 -> None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___199_68  ->
        match uu___199_68 with
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
                 raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | Some effect_id -> FStar_Syntax_Syntax.Reflectable effect_id)
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___200_75  ->
    match uu___200_75 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp : FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___201_83  ->
    match uu___201_83 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____85 -> None
  
let arg_withimp_e imp t = (t, (as_imp imp)) 
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____124 -> (t, None) 
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____134 -> true
            | uu____137 -> false))
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____143 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____148 =
      let uu____149 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____149  in
    FStar_Parser_AST.mk_term uu____148 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____154 =
      let uu____155 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____155  in
    FStar_Parser_AST.mk_term uu____154 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____165 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____165 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____169) ->
          let uu____176 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____176 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____180,uu____181) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____184,uu____185) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____188,t1) -> is_comp_type env t1
      | uu____190 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____203 =
          let uu____205 =
            let uu____206 =
              let uu____209 = FStar_Parser_AST.compile_op n1 s  in
              (uu____209, r)  in
            FStar_Ident.mk_ident uu____206  in
          [uu____205]  in
        FStar_All.pipe_right uu____203 FStar_Ident.lid_of_ids
  
let op_as_term env arity rng op =
  let r l dd =
    let uu____247 =
      let uu____248 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None
         in
      FStar_All.pipe_right uu____248 FStar_Syntax_Syntax.fv_to_tm  in
    Some uu____247  in
  let fallback uu____253 =
    match FStar_Ident.text_of_id op with
    | "=" -> r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational
    | ":=" ->
        r FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_equational
    | "<" -> r FStar_Syntax_Const.op_LT FStar_Syntax_Syntax.Delta_equational
    | "<=" ->
        r FStar_Syntax_Const.op_LTE FStar_Syntax_Syntax.Delta_equational
    | ">" -> r FStar_Syntax_Const.op_GT FStar_Syntax_Syntax.Delta_equational
    | ">=" ->
        r FStar_Syntax_Const.op_GTE FStar_Syntax_Syntax.Delta_equational
    | "&&" ->
        r FStar_Syntax_Const.op_And FStar_Syntax_Syntax.Delta_equational
    | "||" -> r FStar_Syntax_Const.op_Or FStar_Syntax_Syntax.Delta_equational
    | "+" ->
        r FStar_Syntax_Const.op_Addition FStar_Syntax_Syntax.Delta_equational
    | "-" when arity = (Prims.parse_int "1") ->
        r FStar_Syntax_Const.op_Minus FStar_Syntax_Syntax.Delta_equational
    | "-" ->
        r FStar_Syntax_Const.op_Subtraction
          FStar_Syntax_Syntax.Delta_equational
    | "/" ->
        r FStar_Syntax_Const.op_Division FStar_Syntax_Syntax.Delta_equational
    | "%" ->
        r FStar_Syntax_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational
    | "!" ->
        r FStar_Syntax_Const.read_lid FStar_Syntax_Syntax.Delta_equational
    | "@" ->
        let uu____255 = FStar_Options.ml_ish ()  in
        if uu____255
        then
          r FStar_Syntax_Const.list_append_lid
            FStar_Syntax_Syntax.Delta_equational
        else
          r FStar_Syntax_Const.list_tot_append_lid
            FStar_Syntax_Syntax.Delta_equational
    | "^" ->
        r FStar_Syntax_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational
    | "|>" ->
        r FStar_Syntax_Const.pipe_right_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<|" ->
        r FStar_Syntax_Const.pipe_left_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<>" ->
        r FStar_Syntax_Const.op_notEq FStar_Syntax_Syntax.Delta_equational
    | "~" ->
        r FStar_Syntax_Const.not_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "==" ->
        r FStar_Syntax_Const.eq2_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "<<" ->
        r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant
    | "/\\" ->
        r FStar_Syntax_Const.and_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "\\/" ->
        r FStar_Syntax_Const.or_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "==>" ->
        r FStar_Syntax_Const.imp_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "<==>" ->
        r FStar_Syntax_Const.iff_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | uu____258 -> None  in
  let uu____259 =
    let uu____263 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange  in
    FStar_ToSyntax_Env.try_lookup_lid env uu____263  in
  match uu____259 with | Some t -> Some (fst t) | uu____270 -> fallback () 
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____281 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____281
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____306 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____309 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____309 with | (env1,uu____316) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____318,term) ->
          let uu____320 = free_type_vars env term  in (env, uu____320)
      | FStar_Parser_AST.TAnnotated (id,uu____324) ->
          let uu____325 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____325 with | (env1,uu____332) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____335 = free_type_vars env t  in (env, uu____335)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____340 =
        let uu____341 = unparen t  in uu____341.FStar_Parser_AST.tm  in
      match uu____340 with
      | FStar_Parser_AST.Labeled uu____343 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____349 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____349 with | None  -> [a] | uu____356 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____360 -> []
      | FStar_Parser_AST.Uvar uu____361 -> []
      | FStar_Parser_AST.Var uu____362 -> []
      | FStar_Parser_AST.Projector uu____363 -> []
      | FStar_Parser_AST.Discrim uu____366 -> []
      | FStar_Parser_AST.Name uu____367 -> []
      | FStar_Parser_AST.Assign (uu____368,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____371) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____375) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____378,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2])  in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____390,ts) ->
          FStar_List.collect
            (fun uu____400  ->
               match uu____400 with | (t1,uu____405) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____406,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____412) ->
          let uu____413 = free_type_vars env t1  in
          let uu____415 = free_type_vars env t2  in
          FStar_List.append uu____413 uu____415
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____419 = free_type_vars_b env b  in
          (match uu____419 with
           | (env1,f) ->
               let uu____428 = free_type_vars env1 t1  in
               FStar_List.append f uu____428)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____434 =
            FStar_List.fold_left
              (fun uu____441  ->
                 fun binder  ->
                   match uu____441 with
                   | (env1,free) ->
                       let uu____453 = free_type_vars_b env1 binder  in
                       (match uu____453 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____434 with
           | (env1,free) ->
               let uu____471 = free_type_vars env1 body  in
               FStar_List.append free uu____471)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____477 =
            FStar_List.fold_left
              (fun uu____484  ->
                 fun binder  ->
                   match uu____484 with
                   | (env1,free) ->
                       let uu____496 = free_type_vars_b env1 binder  in
                       (match uu____496 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____477 with
           | (env1,free) ->
               let uu____514 = free_type_vars env1 body  in
               FStar_List.append free uu____514)
      | FStar_Parser_AST.Project (t1,uu____517) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____520 -> []
      | FStar_Parser_AST.Let uu____524 -> []
      | FStar_Parser_AST.LetOpen uu____531 -> []
      | FStar_Parser_AST.If uu____534 -> []
      | FStar_Parser_AST.QForall uu____538 -> []
      | FStar_Parser_AST.QExists uu____545 -> []
      | FStar_Parser_AST.Record uu____552 -> []
      | FStar_Parser_AST.Match uu____559 -> []
      | FStar_Parser_AST.TryWith uu____567 -> []
      | FStar_Parser_AST.Bind uu____575 -> []
      | FStar_Parser_AST.Seq uu____579 -> []

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____609 =
        let uu____610 = unparen t1  in uu____610.FStar_Parser_AST.tm  in
      match uu____609 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____634 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____650 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____650  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____664 =
                     let uu____665 =
                       let uu____668 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____668)  in
                     FStar_Parser_AST.TAnnotated uu____665  in
                   FStar_Parser_AST.mk_binder uu____664 x.FStar_Ident.idRange
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
        let uu____681 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____681  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____695 =
                     let uu____696 =
                       let uu____699 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____699)  in
                     FStar_Parser_AST.TAnnotated uu____696  in
                   FStar_Parser_AST.mk_binder uu____695 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____701 =
             let uu____702 = unparen t  in uu____702.FStar_Parser_AST.tm  in
           match uu____701 with
           | FStar_Parser_AST.Product uu____703 -> t
           | uu____707 ->
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
      | uu____730 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____736,uu____737) -> true
    | FStar_Parser_AST.PatVar (uu____740,uu____741) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____745) -> is_var_pattern p1
    | uu____746 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____752) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____753;
           FStar_Parser_AST.prange = uu____754;_},uu____755)
        -> true
    | uu____761 -> false
  
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
    | uu____766 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____795 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____795 with
             | (name,args,uu____812) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____826);
               FStar_Parser_AST.prange = uu____827;_},args)
            when is_top_level1 ->
            let uu____833 =
              let uu____836 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____836  in
            (uu____833, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____842);
               FStar_Parser_AST.prange = uu____843;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____853 -> failwith "Not an app pattern"
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____879 -> acc
      | FStar_Parser_AST.PatVar (uu____880,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____882 -> acc
      | FStar_Parser_AST.PatTvar uu____883 -> acc
      | FStar_Parser_AST.PatOp uu____887 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____893) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____899) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____908 = FStar_List.map FStar_Pervasives.snd guarded_pats
             in
          gather_pattern_bound_vars_from_list uu____908
      | FStar_Parser_AST.PatAscribed (pat,uu____913) ->
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
      (fun uu____923  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____944 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____966 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___202_986  ->
    match uu___202_986 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____991 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___203_1011  ->
        match uu___203_1011 with
        | (None ,k) ->
            let uu____1020 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1020, env)
        | (Some a,k) ->
            let uu____1024 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____1024 with
             | (env1,a1) ->
                 (((let uu___224_1035 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___224_1035.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___224_1035.FStar_Syntax_Syntax.index);
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
  fun uu____1049  ->
    match uu____1049 with
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
    let uu____1098 =
      let uu____1108 =
        let uu____1109 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1109  in
      let uu____1110 =
        let uu____1116 =
          let uu____1121 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1121)  in
        [uu____1116]  in
      (uu____1108, uu____1110)  in
    FStar_Syntax_Syntax.Tm_app uu____1098  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____1157 =
      let uu____1167 =
        let uu____1168 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1168  in
      let uu____1169 =
        let uu____1175 =
          let uu____1180 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1180)  in
        [uu____1175]  in
      (uu____1167, uu____1169)  in
    FStar_Syntax_Syntax.Tm_app uu____1157  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1232 =
      let uu____1242 =
        let uu____1243 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1243  in
      let uu____1244 =
        let uu____1250 =
          let uu____1255 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1255)  in
        let uu____1258 =
          let uu____1264 =
            let uu____1269 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1269)  in
          [uu____1264]  in
        uu____1250 :: uu____1258  in
      (uu____1242, uu____1244)  in
    FStar_Syntax_Syntax.Tm_app uu____1232  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___204_1296  ->
    match uu___204_1296 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1297 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1307 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1307)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1320 =
      let uu____1321 = unparen t  in uu____1321.FStar_Parser_AST.tm  in
    match uu____1320 with
    | FStar_Parser_AST.Wild  ->
        let uu____1324 =
          let uu____1325 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1325  in
        FStar_Util.Inr uu____1324
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1330)) ->
        let n1 = FStar_Util.int_of_string repr  in
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
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____1369 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1369
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1376 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1376
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1383 =
               let uu____1384 =
                 let uu____1387 =
                   let uu____1388 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1388
                    in
                 (uu____1387, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1384  in
             raise uu____1383)
    | FStar_Parser_AST.App uu____1391 ->
        let rec aux t1 univargs =
          let uu____1410 =
            let uu____1411 = unparen t1  in uu____1411.FStar_Parser_AST.tm
             in
          match uu____1410 with
          | FStar_Parser_AST.App (t2,targ,uu____1416) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___205_1428  ->
                     match uu___205_1428 with
                     | FStar_Util.Inr uu____1431 -> true
                     | uu____1432 -> false) univargs
              then
                let uu____1435 =
                  let uu____1436 =
                    FStar_List.map
                      (fun uu___206_1440  ->
                         match uu___206_1440 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1436  in
                FStar_Util.Inr uu____1435
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___207_1450  ->
                        match uu___207_1450 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1454 -> failwith "impossible")
                     univargs
                    in
                 let uu____1455 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1455)
          | uu____1459 ->
              let uu____1460 =
                let uu____1461 =
                  let uu____1464 =
                    let uu____1465 =
                      let uu____1466 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1466 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1465  in
                  (uu____1464, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1461  in
              raise uu____1460
           in
        aux t []
    | uu____1471 ->
        let uu____1472 =
          let uu____1473 =
            let uu____1476 =
              let uu____1477 =
                let uu____1478 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1478 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1477  in
            (uu____1476, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1473  in
        raise uu____1472
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1517 = FStar_List.hd fields  in
  match uu____1517 with
  | (f,uu____1523) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
           in
        let check_field uu____1531 =
          match uu____1531 with
          | (f',uu____1535) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1537 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record  in
                if uu____1537
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str
                      in
                   raise (FStar_Errors.Error (msg, rg)))))
           in
        (let uu____1541 = FStar_List.tl fields  in
         FStar_List.iter check_field uu____1541);
        (match () with | () -> record)))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____1701 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1706 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1707 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1709,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1731  ->
                          match uu____1731 with
                          | (p3,uu____1737) ->
                              let uu____1738 = pat_vars p3  in
                              FStar_Util.set_union out uu____1738)
                     FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1741) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1742) -> ()
         | (true ,uu____1746) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1774 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1774 with
           | Some y -> (l, e, y)
           | uu____1782 ->
               let uu____1784 = push_bv_maybe_mut e x  in
               (match uu____1784 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
           | FStar_Parser_AST.PatOr uu____1832 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1842 =
                 let uu____1843 =
                   let uu____1844 =
                     let uu____1848 =
                       let uu____1849 =
                         let uu____1852 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText
                            in
                         (uu____1852, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____1849  in
                     (uu____1848, None)  in
                   FStar_Parser_AST.PatVar uu____1844  in
                 {
                   FStar_Parser_AST.pat = uu____1843;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1842
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1856 = aux loc env1 p2  in
               (match uu____1856 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1881 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1887 = close_fun env1 t  in
                            desugar_term env1 uu____1887  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1889 -> true)
                           then
                             (let uu____1890 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1891 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1892 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1890 uu____1891 uu____1892)
                           else ();
                           LocalBinder
                             (((let uu___225_1894 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_1894.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_1894.FStar_Syntax_Syntax.index);
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
               let uu____1898 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1898, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1908 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1908, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1924 = resolvex loc env1 x  in
               (match uu____1924 with
                | (loc1,env2,xbv) ->
                    let uu____1938 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1938, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1954 = resolvex loc env1 x  in
               (match uu____1954 with
                | (loc1,env2,xbv) ->
                    let uu____1968 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1968, imp))
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
               let uu____1979 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1979, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1997;_},args)
               ->
               let uu____2001 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2019  ->
                        match uu____2019 with
                        | (loc1,env2,args1) ->
                            let uu____2049 = aux loc1 env2 arg  in
                            (match uu____2049 with
                             | (loc2,env3,uu____2067,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2001 with
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
                    let uu____2116 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____2116, false))
           | FStar_Parser_AST.PatApp uu____2129 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2142 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2156  ->
                        match uu____2156 with
                        | (loc1,env2,pats1) ->
                            let uu____2178 = aux loc1 env2 pat  in
                            (match uu____2178 with
                             | (loc2,env3,uu____2194,pat1,uu____2196) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____2142 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2230 =
                        let uu____2233 =
                          let uu____2238 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2238  in
                        let uu____2239 =
                          let uu____2240 =
                            let uu____2248 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2248, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2240  in
                        FStar_All.pipe_left uu____2233 uu____2239  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2271 =
                               let uu____2272 =
                                 let uu____2280 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2280, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2272  in
                             FStar_All.pipe_left (pos_r r) uu____2271) pats1
                        uu____2230
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2312 =
                 FStar_List.fold_left
                   (fun uu____2329  ->
                      fun p2  ->
                        match uu____2329 with
                        | (loc1,env2,pats) ->
                            let uu____2360 = aux loc1 env2 p2  in
                            (match uu____2360 with
                             | (loc2,env3,uu____2378,pat,uu____2380) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2312 with
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
                    let uu____2457 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2457 with
                     | (constr,uu____2470) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2473 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2475 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2475,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2516  ->
                         match uu____2516 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2531  ->
                         match uu____2531 with
                         | (f,uu____2535) ->
                             let uu____2536 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2548  ->
                                       match uu____2548 with
                                       | (g,uu____2552) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2536 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2555,p2) -> p2)))
                  in
               let app =
                 let uu____2560 =
                   let uu____2561 =
                     let uu____2565 =
                       let uu____2566 =
                         let uu____2567 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2567  in
                       FStar_Parser_AST.mk_pattern uu____2566
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2565, args)  in
                   FStar_Parser_AST.PatApp uu____2561  in
                 FStar_Parser_AST.mk_pattern uu____2560
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2569 = aux loc env1 app  in
               (match uu____2569 with
                | (env2,e,b,p2,uu____2588) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2610 =
                            let uu____2611 =
                              let uu____2619 =
                                let uu___226_2620 = fv  in
                                let uu____2621 =
                                  let uu____2623 =
                                    let uu____2624 =
                                      let uu____2628 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2628)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2624
                                     in
                                  Some uu____2623  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___226_2620.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___226_2620.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2621
                                }  in
                              (uu____2619, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2611  in
                          FStar_All.pipe_left pos uu____2610
                      | uu____2647 -> p2  in
                    (env2, e, b, p3, false))
            in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2680 = aux loc env1 p2  in
               (match uu____2680 with
                | (loc1,env2,var,p3,uu____2698) ->
                    let uu____2703 =
                      FStar_List.fold_left
                        (fun uu____2716  ->
                           fun p4  ->
                             match uu____2716 with
                             | (loc2,env3,ps1) ->
                                 let uu____2739 = aux loc2 env3 p4  in
                                 (match uu____2739 with
                                  | (loc3,env4,uu____2755,p5,uu____2757) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____2703 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____2798 ->
               let uu____2799 = aux loc env1 p1  in
               (match uu____2799 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____2829 = aux_maybe_or env p  in
         match uu____2829 with
         | (env1,b,pats) ->
             ((let uu____2850 =
                 FStar_List.map check_linear_pattern_variables pats  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2850);
              (env1, b, pats)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2873 =
              let uu____2874 =
                let uu____2877 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2877, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2874  in
            (env, uu____2873, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2888 =
                  let uu____2889 =
                    let uu____2892 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText
                       in
                    (uu____2892, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____2889  in
                mklet uu____2888
            | FStar_Parser_AST.PatVar (x,uu____2894) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2898);
                   FStar_Parser_AST.prange = uu____2899;_},t)
                ->
                let uu____2903 =
                  let uu____2904 =
                    let uu____2907 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2908 = desugar_term env t  in
                    (uu____2907, uu____2908)  in
                  LetBinder uu____2904  in
                (env, uu____2903, [])
            | uu____2910 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2916 = desugar_data_pat env p is_mut  in
             match uu____2916 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2933;
                       FStar_Syntax_Syntax.ty = uu____2934;
                       FStar_Syntax_Syntax.p = uu____2935;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2940;
                       FStar_Syntax_Syntax.ty = uu____2941;
                       FStar_Syntax_Syntax.p = uu____2942;_}::[] -> []
                   | uu____2947 -> p1  in
                 (env1, binder, p2))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun uu____2952  ->
    fun env  ->
      fun pat  ->
        let uu____2955 = desugar_data_pat env pat false  in
        match uu____2955 with | (env1,uu____2964,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat Prims.list)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true  in
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
      fun uu____2979  ->
        fun range  ->
          match uu____2979 with
          | (signedness,width) ->
              let uu____2987 = FStar_Const.bounds signedness width  in
              (match uu____2987 with
               | (lower,upper) ->
                   let value =
                     let uu____2995 = FStar_Util.ensure_decimal repr  in
                     FStar_Util.int_of_string uu____2995  in
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
                              | FStar_Const.Int64  -> "64")))
                      in
                   (if
                      Prims.op_Negation
                        ((lower <= value) && (value <= upper))
                    then
                      (let uu____2998 =
                         let uu____2999 =
                           let uu____3002 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm
                              in
                           (uu____3002, range)  in
                         FStar_Errors.Error uu____2999  in
                       raise uu____2998)
                    else ();
                    (let private_intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat ".__"
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t"))
                        in
                     let intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat "."
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t"))
                        in
                     let lid =
                       FStar_Ident.lid_of_path
                         (FStar_Ident.path_of_text intro_nm) range
                        in
                     let lid1 =
                       let uu____3010 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid  in
                       match uu____3010 with
                       | Some (intro_term,uu____3017) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range
                                   in
                                let private_fv =
                                  let uu____3025 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta
                                     in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____3025 fv.FStar_Syntax_Syntax.fv_qual
                                   in
                                let uu___227_3026 = intro_term  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___227_3026.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___227_3026.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___227_3026.FStar_Syntax_Syntax.vars)
                                }
                            | uu____3031 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____3036 =
                             FStar_Util.format1 "%s not in scope\n" tnm  in
                           failwith uu____3036
                        in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range
                        in
                     let uu____3055 =
                       let uu____3058 =
                         let uu____3059 =
                           let uu____3069 =
                             let uu____3075 =
                               let uu____3080 =
                                 FStar_Syntax_Syntax.as_implicit false  in
                               (repr1, uu____3080)  in
                             [uu____3075]  in
                           (lid1, uu____3069)  in
                         FStar_Syntax_Syntax.Tm_app uu____3059  in
                       FStar_Syntax_Syntax.mk uu____3058  in
                     uu____3055 None range)))

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
            let uu____3117 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____3117 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____3135 =
                    let uu____3136 =
                      let uu____3141 = mk_ref_read tm1  in
                      (uu____3141,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____3136  in
                  FStar_All.pipe_left mk1 uu____3135
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3155 =
          let uu____3156 = unparen t  in uu____3156.FStar_Parser_AST.tm  in
        match uu____3155 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3157; FStar_Ident.ident = uu____3158;
              FStar_Ident.nsstr = uu____3159; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3161 ->
            let uu____3162 =
              let uu____3163 =
                let uu____3166 =
                  let uu____3167 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____3167  in
                (uu____3166, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____3163  in
            raise uu____3162
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
          let uu___228_3195 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___228_3195.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___228_3195.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___228_3195.FStar_Syntax_Syntax.vars)
          }  in
        let uu____3202 =
          let uu____3203 = unparen top  in uu____3203.FStar_Parser_AST.tm  in
        match uu____3202 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3204 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int (i,Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____3236::uu____3237::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3239 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____3239 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3248;_},t1::t2::[])
                  ->
                  let uu____3252 = flatten1 t1  in
                  FStar_List.append uu____3252 [t2]
              | uu____3254 -> [t]  in
            let targs =
              let uu____3257 =
                let uu____3259 = unparen top  in flatten1 uu____3259  in
              FStar_All.pipe_right uu____3257
                (FStar_List.map
                   (fun t  ->
                      let uu____3263 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____3263))
               in
            let uu____3264 =
              let uu____3267 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3267
               in
            (match uu____3264 with
             | (tup,uu____3277) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3280 =
              let uu____3283 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              fst uu____3283  in
            FStar_All.pipe_left setpos uu____3280
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3297 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____3297 with
             | None  ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: "
                          (FStar_Ident.text_of_id s)),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____3324 = desugar_term env t  in
                             (uu____3324, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3333)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3341 =
              let uu___229_3342 = top  in
              let uu____3343 =
                let uu____3344 =
                  let uu____3348 =
                    let uu___230_3349 = top  in
                    let uu____3350 =
                      let uu____3351 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3351  in
                    {
                      FStar_Parser_AST.tm = uu____3350;
                      FStar_Parser_AST.range =
                        (uu___230_3349.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3349.FStar_Parser_AST.level)
                    }  in
                  (uu____3348, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3344  in
              {
                FStar_Parser_AST.tm = uu____3343;
                FStar_Parser_AST.range =
                  (uu___229_3342.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3342.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3341
        | FStar_Parser_AST.Construct (n1,(a,uu____3354)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3362 =
              let uu___231_3363 = top  in
              let uu____3364 =
                let uu____3365 =
                  let uu____3369 =
                    let uu___232_3370 = top  in
                    let uu____3371 =
                      let uu____3372 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3372  in
                    {
                      FStar_Parser_AST.tm = uu____3371;
                      FStar_Parser_AST.range =
                        (uu___232_3370.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3370.FStar_Parser_AST.level)
                    }  in
                  (uu____3369, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3365  in
              {
                FStar_Parser_AST.tm = uu____3364;
                FStar_Parser_AST.range =
                  (uu___231_3363.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3363.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3362
        | FStar_Parser_AST.Construct (n1,(a,uu____3375)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3383 =
              let uu___233_3384 = top  in
              let uu____3385 =
                let uu____3386 =
                  let uu____3390 =
                    let uu___234_3391 = top  in
                    let uu____3392 =
                      let uu____3393 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3393  in
                    {
                      FStar_Parser_AST.tm = uu____3392;
                      FStar_Parser_AST.range =
                        (uu___234_3391.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3391.FStar_Parser_AST.level)
                    }  in
                  (uu____3390, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3386  in
              {
                FStar_Parser_AST.tm = uu____3385;
                FStar_Parser_AST.range =
                  (uu___233_3384.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3384.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3383
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3394; FStar_Ident.ident = uu____3395;
              FStar_Ident.nsstr = uu____3396; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3398; FStar_Ident.ident = uu____3399;
              FStar_Ident.nsstr = uu____3400; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3402; FStar_Ident.ident = uu____3403;
               FStar_Ident.nsstr = uu____3404; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3414 =
              let uu____3415 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____3415  in
            mk1 uu____3414
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3416; FStar_Ident.ident = uu____3417;
              FStar_Ident.nsstr = uu____3418; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3420; FStar_Ident.ident = uu____3421;
              FStar_Ident.nsstr = uu____3422; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3424; FStar_Ident.ident = uu____3425;
              FStar_Ident.nsstr = uu____3426; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3430;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3432 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____3432 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3436 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____3436))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____3440 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____3440 with
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
                let uu____3460 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____3460 with
                | Some uu____3465 -> Some (true, l)
                | None  ->
                    let uu____3468 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____3468 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3476 -> None)
                 in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3484 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____3484
              | uu____3485 ->
                  let uu____3489 =
                    let uu____3490 =
                      let uu____3493 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str
                         in
                      (uu____3493, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3490  in
                  raise uu____3489))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3496 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____3496 with
              | None  ->
                  let uu____3498 =
                    let uu____3499 =
                      let uu____3502 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str
                         in
                      (uu____3502, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3499  in
                  raise uu____3498
              | uu____3503 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3515 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____3515 with
              | Some head1 ->
                  let uu____3518 =
                    let uu____3523 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____3523, true)  in
                  (match uu____3518 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3536 ->
                            let uu____3540 =
                              FStar_Util.take
                                (fun uu____3551  ->
                                   match uu____3551 with
                                   | (uu____3554,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____3540 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3587  ->
                                        match uu____3587 with
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
                    let uu____3619 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____3619 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3621 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position")
                     in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3626 =
              FStar_List.fold_left
                (fun uu____3643  ->
                   fun b  ->
                     match uu____3643 with
                     | (env1,tparams,typs) ->
                         let uu____3674 = desugar_binder env1 b  in
                         (match uu____3674 with
                          | (xopt,t1) ->
                              let uu____3690 =
                                match xopt with
                                | None  ->
                                    let uu____3695 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3695)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3690 with
                               | (env2,x) ->
                                   let uu____3707 =
                                     let uu____3709 =
                                       let uu____3711 =
                                         let uu____3712 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3712
                                          in
                                       [uu____3711]  in
                                     FStar_List.append typs uu____3709  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___235_3725 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___235_3725.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___235_3725.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3707))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3626 with
             | (env1,uu____3738,targs) ->
                 let uu____3750 =
                   let uu____3753 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3753
                    in
                 (match uu____3750 with
                  | (tup,uu____3763) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3771 = uncurry binders t  in
            (match uu____3771 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___208_3794 =
                   match uu___208_3794 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3804 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3804
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3820 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3820 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3831 = desugar_binder env b  in
            (match uu____3831 with
             | (None ,uu____3835) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3841 = as_binder env None b1  in
                 (match uu____3841 with
                  | ((x,uu____3845),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3850 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3850))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3865 =
              FStar_List.fold_left
                (fun uu____3872  ->
                   fun pat  ->
                     match uu____3872 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3887,t) ->
                              let uu____3889 =
                                let uu____3891 = free_type_vars env1 t  in
                                FStar_List.append uu____3891 ftvs  in
                              (env1, uu____3889)
                          | uu____3894 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3865 with
             | (uu____3897,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3905 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3905 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___209_3934 =
                   match uu___209_3934 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3963 =
                                 let uu____3964 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3964
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3963 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____4006 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____4006
                   | p::rest ->
                       let uu____4014 = desugar_binding_pat env1 p  in
                       (match uu____4014 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____4030 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange)))
                               in
                            let uu____4033 =
                              match b with
                              | LetBinder uu____4052 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____4083) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____4106 =
                                          let uu____4109 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____4109, p1)  in
                                        Some uu____4106
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4134,uu____4135) ->
                                             let tup2 =
                                               let uu____4137 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4137
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4141 =
                                                 let uu____4144 =
                                                   let uu____4145 =
                                                     let uu____4155 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____4158 =
                                                       let uu____4160 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____4161 =
                                                         let uu____4163 =
                                                           let uu____4164 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4164
                                                            in
                                                         [uu____4163]  in
                                                       uu____4160 ::
                                                         uu____4161
                                                        in
                                                     (uu____4155, uu____4158)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4145
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4144
                                                  in
                                               uu____4141 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____4179 =
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
                                                 uu____4179
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4199,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4201,pats)) ->
                                             let tupn =
                                               let uu____4228 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4228
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4240 =
                                                 let uu____4241 =
                                                   let uu____4251 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____4254 =
                                                     let uu____4260 =
                                                       let uu____4266 =
                                                         let uu____4267 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4267
                                                          in
                                                       [uu____4266]  in
                                                     FStar_List.append args
                                                       uu____4260
                                                      in
                                                   (uu____4251, uu____4254)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4241
                                                  in
                                               mk1 uu____4240  in
                                             let p2 =
                                               let uu____4282 =
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
                                                 uu____4282
                                                in
                                             Some (sc1, p2)
                                         | uu____4306 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____4033 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4347,uu____4348,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4360 =
                let uu____4361 = unparen e  in uu____4361.FStar_Parser_AST.tm
                 in
              match uu____4360 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____4367 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4371;
               FStar_Parser_AST.level = uu____4372;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Syntax_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4375 =
                let uu____4376 = unparen top  in
                uu____4376.FStar_Parser_AST.tm  in
              match uu____4375 with
              | FStar_Parser_AST.App (l,uu____4378,uu____4379) -> l
              | uu____4380 -> failwith "impossible"  in
            let tactic_unit_type =
              let uu____4382 =
                let uu____4383 =
                  let uu____4387 =
                    let uu____4388 =
                      let uu____4389 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4389  in
                    FStar_Parser_AST.mk_term uu____4388
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level
                     in
                  let uu____4390 =
                    let uu____4391 =
                      let uu____4392 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4392  in
                    FStar_Parser_AST.mk_term uu____4391
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level
                     in
                  (uu____4387, uu____4390, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4383  in
              FStar_Parser_AST.mk_term uu____4382 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level
               in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type, None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term env t'
        | FStar_Parser_AST.App uu____4395 ->
            let rec aux args e =
              let uu____4416 =
                let uu____4417 = unparen e  in uu____4417.FStar_Parser_AST.tm
                 in
              match uu____4416 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4427 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4427  in
                  aux (arg :: args) e1
              | uu____4434 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (x, None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind1 =
              let uu____4451 =
                let uu____4452 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
                FStar_Parser_AST.Var uu____4452  in
              FStar_Parser_AST.mk_term uu____4451 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr
               in
            let uu____4453 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term env uu____4453
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4456 =
              let uu____4457 =
                let uu____4462 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____4462,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____4457  in
            mk1 uu____4456
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____4473 =
              let uu____4478 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____4478 then desugar_typ else desugar_term  in
            uu____4473 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____4503 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4545  ->
                        match uu____4545 with
                        | (p,def) ->
                            let uu____4559 = is_app_pattern p  in
                            if uu____4559
                            then
                              let uu____4569 =
                                destruct_app_pattern env top_level p  in
                              (uu____4569, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4598 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4598, def1)
                               | uu____4613 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4627);
                                           FStar_Parser_AST.prange =
                                             uu____4628;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4641 =
                                            let uu____4649 =
                                              let uu____4652 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4652  in
                                            (uu____4649, [], (Some t))  in
                                          (uu____4641, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4677)
                                        ->
                                        if top_level
                                        then
                                          let uu____4689 =
                                            let uu____4697 =
                                              let uu____4700 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4700  in
                                            (uu____4697, [], None)  in
                                          (uu____4689, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4724 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4734 =
                FStar_List.fold_left
                  (fun uu____4758  ->
                     fun uu____4759  ->
                       match (uu____4758, uu____4759) with
                       | ((env1,fnames,rec_bindings),((f,uu____4803,uu____4804),uu____4805))
                           ->
                           let uu____4845 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4859 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4859 with
                                  | (env2,xx) ->
                                      let uu____4870 =
                                        let uu____4872 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4872 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4870))
                             | FStar_Util.Inr l ->
                                 let uu____4877 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4877, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4845 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4734 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4950 =
                    match uu____4950 with
                    | ((uu____4962,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4988 = is_comp_type env1 t  in
                                if uu____4988
                                then
                                  ((let uu____4990 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4995 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4995))
                                       in
                                    match uu____4990 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4998 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4999 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4999))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4998
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____5006 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____5006 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____5009 ->
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
                              let uu____5019 =
                                let uu____5020 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____5020
                                  None
                                 in
                              FStar_Util.Inr uu____5019
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
                  let uu____5040 =
                    let uu____5041 =
                      let uu____5049 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____5049)  in
                    FStar_Syntax_Syntax.Tm_let uu____5041  in
                  FStar_All.pipe_left mk1 uu____5040
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____5076 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____5076 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____5097 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____5097 None  in
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
                    | LocalBinder (x,uu____5105) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____5108;
                              FStar_Syntax_Syntax.ty = uu____5109;
                              FStar_Syntax_Syntax.p = uu____5110;_}::[] ->
                              body1
                          | uu____5115 ->
                              let uu____5117 =
                                let uu____5120 =
                                  let uu____5121 =
                                    let uu____5137 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____5138 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1
                                       in
                                    (uu____5137, uu____5138)  in
                                  FStar_Syntax_Syntax.Tm_match uu____5121  in
                                FStar_Syntax_Syntax.mk uu____5120  in
                              uu____5117 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____5151 =
                          let uu____5152 =
                            let uu____5160 =
                              let uu____5161 =
                                let uu____5162 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____5162]  in
                              FStar_Syntax_Subst.close uu____5161 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5160)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____5152  in
                        FStar_All.pipe_left mk1 uu____5151
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
            let uu____5182 = is_rec || (is_app_pattern pat)  in
            if uu____5182
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____5191 =
                let uu____5192 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____5192  in
              mk1 uu____5191  in
            let uu____5193 =
              let uu____5194 =
                let uu____5210 =
                  let uu____5213 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____5213
                    ((FStar_Util.Inl t_bool1), None)
                   in
                let uu____5231 =
                  let uu____5241 =
                    let uu____5250 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____5253 = desugar_term env t2  in
                    (uu____5250, None, uu____5253)  in
                  let uu____5261 =
                    let uu____5271 =
                      let uu____5280 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____5283 = desugar_term env t3  in
                      (uu____5280, None, uu____5283)  in
                    [uu____5271]  in
                  uu____5241 :: uu____5261  in
                (uu____5210, uu____5231)  in
              FStar_Syntax_Syntax.Tm_match uu____5194  in
            mk1 uu____5193
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
            let desugar_branch uu____5372 =
              match uu____5372 with
              | (pat,wopt,b) ->
                  let uu____5383 = desugar_match_pat env pat  in
                  (match uu____5383 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5396 = desugar_term env1 e1  in
                             Some uu____5396
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____5398 =
              let uu____5399 =
                let uu____5415 = desugar_term env e  in
                let uu____5416 = FStar_List.collect desugar_branch branches
                   in
                (uu____5415, uu____5416)  in
              FStar_Syntax_Syntax.Tm_match uu____5399  in
            FStar_All.pipe_left mk1 uu____5398
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5435 = is_comp_type env t  in
              if uu____5435
              then
                let uu____5440 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____5440
              else
                (let uu____5446 = desugar_term env t  in
                 FStar_Util.Inl uu____5446)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____5451 =
              let uu____5452 =
                let uu____5470 = desugar_term env e  in
                (uu____5470, (annot, tac_opt1), None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____5452  in
            FStar_All.pipe_left mk1 uu____5451
        | FStar_Parser_AST.Record (uu____5486,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____5507 = FStar_List.hd fields  in
              match uu____5507 with | (f,uu____5514) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5538  ->
                        match uu____5538 with
                        | (g,uu____5542) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____5546,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5554 =
                         let uu____5555 =
                           let uu____5558 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____5558, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____5555  in
                       raise uu____5554
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
                  let uu____5564 =
                    let uu____5570 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5584  ->
                              match uu____5584 with
                              | (f,uu____5590) ->
                                  let uu____5591 =
                                    let uu____5592 = get_field None f  in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5592
                                     in
                                  (uu____5591, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____5570)  in
                  FStar_Parser_AST.Construct uu____5564
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5603 =
                      let uu____5604 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5604  in
                    FStar_Parser_AST.mk_term uu____5603 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5606 =
                      let uu____5613 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5627  ->
                                match uu____5627 with
                                | (f,uu____5633) -> get_field (Some xterm) f))
                         in
                      (None, uu____5613)  in
                    FStar_Parser_AST.Record uu____5606  in
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
                         FStar_Syntax_Syntax.tk = uu____5649;
                         FStar_Syntax_Syntax.pos = uu____5650;
                         FStar_Syntax_Syntax.vars = uu____5651;_},args);
                    FStar_Syntax_Syntax.tk = uu____5653;
                    FStar_Syntax_Syntax.pos = uu____5654;
                    FStar_Syntax_Syntax.vars = uu____5655;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5677 =
                     let uu____5678 =
                       let uu____5688 =
                         let uu____5689 =
                           let uu____5691 =
                             let uu____5692 =
                               let uu____5696 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5696)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5692  in
                           Some uu____5691  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5689
                          in
                       (uu____5688, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5678  in
                   FStar_All.pipe_left mk1 uu____5677  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5720 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5724 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____5724 with
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
                  let uu____5737 =
                    let uu____5738 =
                      let uu____5748 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1
                         in
                      let uu____5749 =
                        let uu____5751 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____5751]  in
                      (uu____5748, uu____5749)  in
                    FStar_Syntax_Syntax.Tm_app uu____5738  in
                  FStar_All.pipe_left mk1 uu____5737))
        | FStar_Parser_AST.NamedTyp (uu____5755,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5758 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5759 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5760,uu____5761,uu____5762) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5769,uu____5770,uu____5771) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5778,uu____5779,uu____5780) ->
            failwith "Not implemented yet"

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier option)
        Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5804  ->
              match uu____5804 with
              | (a,imp) ->
                  let uu____5812 = desugar_term env a  in
                  arg_withimp_e imp uu____5812))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5829 =
          match uu____5829 with
          | (t1,uu____5833) ->
              let uu____5834 =
                let uu____5835 = unparen t1  in
                uu____5835.FStar_Parser_AST.tm  in
              (match uu____5834 with
               | FStar_Parser_AST.Requires uu____5836 -> true
               | uu____5840 -> false)
           in
        let is_ensures uu____5846 =
          match uu____5846 with
          | (t1,uu____5850) ->
              let uu____5851 =
                let uu____5852 = unparen t1  in
                uu____5852.FStar_Parser_AST.tm  in
              (match uu____5851 with
               | FStar_Parser_AST.Ensures uu____5853 -> true
               | uu____5857 -> false)
           in
        let is_app head1 uu____5866 =
          match uu____5866 with
          | (t1,uu____5870) ->
              let uu____5871 =
                let uu____5872 = unparen t1  in
                uu____5872.FStar_Parser_AST.tm  in
              (match uu____5871 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5874;
                      FStar_Parser_AST.level = uu____5875;_},uu____5876,uu____5877)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5878 -> false)
           in
        let is_smt_pat uu____5884 =
          match uu____5884 with
          | (t1,uu____5888) ->
              let uu____5889 =
                let uu____5890 = unparen t1  in
                uu____5890.FStar_Parser_AST.tm  in
              (match uu____5889 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5893);
                             FStar_Parser_AST.range = uu____5894;
                             FStar_Parser_AST.level = uu____5895;_},uu____5896)::uu____5897::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____5918;
                             FStar_Parser_AST.level = uu____5919;_},uu____5920)::uu____5921::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5934 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5952 = head_and_args t1  in
          match uu____5952 with
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____6169 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____6169, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6183 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6183
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6192 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6192
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
               | uu____6212 ->
                   let default_effect =
                     let uu____6214 = FStar_Options.ml_ish ()  in
                     if uu____6214
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6217 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____6217
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____6230 = pre_process_comp_typ t  in
        match uu____6230 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6262 =
                  let uu____6263 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6263
                   in
                fail uu____6262)
             else ();
             (let is_universe uu____6270 =
                match uu____6270 with
                | (uu____6273,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____6275 = FStar_Util.take is_universe args  in
              match uu____6275 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6306  ->
                         match uu____6306 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____6311 =
                    let uu____6319 = FStar_List.hd args1  in
                    let uu____6324 = FStar_List.tl args1  in
                    (uu____6319, uu____6324)  in
                  (match uu____6311 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg)  in
                       let rest1 = desugar_args env rest  in
                       let uu____6355 =
                         let is_decrease uu____6378 =
                           match uu____6378 with
                           | (t1,uu____6385) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6393;
                                       FStar_Syntax_Syntax.pos = uu____6394;
                                       FStar_Syntax_Syntax.vars = uu____6395;_},uu____6396::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6418 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____6355 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6484  ->
                                      match uu____6484 with
                                      | (t1,uu____6491) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6498,(arg,uu____6500)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6522 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6534 -> false  in
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
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   None
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6637 -> pat  in
                                         let uu____6638 =
                                           let uu____6645 =
                                             let uu____6652 =
                                               let uu____6658 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____6658, aq)  in
                                             [uu____6652]  in
                                           ens :: uu____6645  in
                                         req :: uu____6638
                                     | uu____6694 -> rest2
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
        | uu____6710 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___236_6735 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___236_6735.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___236_6735.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___236_6735.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___237_6765 = b  in
             {
               FStar_Parser_AST.b = (uu___237_6765.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___237_6765.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___237_6765.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6798 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6798)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6807 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6807 with
             | (env1,a1) ->
                 let a2 =
                   let uu___238_6815 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___238_6815.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___238_6815.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6828 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6837 =
                     let uu____6840 =
                       let uu____6841 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6841]  in
                     no_annot_abs uu____6840 body2  in
                   FStar_All.pipe_left setpos uu____6837  in
                 let uu____6846 =
                   let uu____6847 =
                     let uu____6857 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6858 =
                       let uu____6860 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6860]  in
                     (uu____6857, uu____6858)  in
                   FStar_Syntax_Syntax.Tm_app uu____6847  in
                 FStar_All.pipe_left mk1 uu____6846)
        | uu____6864 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6913 = q (rest, pats, body)  in
              let uu____6917 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6913 uu____6917
                FStar_Parser_AST.Formula
               in
            let uu____6918 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6918 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6923 -> failwith "impossible"  in
      let uu____6925 =
        let uu____6926 = unparen f  in uu____6926.FStar_Parser_AST.tm  in
      match uu____6925 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6933,uu____6934) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6940,uu____6941) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6960 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6960
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6981 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6981
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____7006 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____7010 =
        FStar_List.fold_left
          (fun uu____7023  ->
             fun b  ->
               match uu____7023 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___239_7051 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___239_7051.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___239_7051.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___239_7051.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____7061 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____7061 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___240_7073 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___240_7073.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___240_7073.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____7082 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____7010 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____7132 = desugar_typ env t  in ((Some x), uu____7132)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7136 = desugar_typ env t  in ((Some x), uu____7136)
      | FStar_Parser_AST.TVariable x ->
          let uu____7139 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____7139)
      | FStar_Parser_AST.NoName t ->
          let uu____7154 = desugar_typ env t  in (None, uu____7154)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators :
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
               (fun uu___210_7179  ->
                  match uu___210_7179 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7180 -> false))
           in
        let quals2 q =
          let uu____7188 =
            (let uu____7189 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____7189) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____7188
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____7196 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7196;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
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
            let uu____7225 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7235  ->
                        match uu____7235 with
                        | (x,uu____7240) ->
                            let uu____7241 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____7241 with
                             | (field_name,uu____7246) ->
                                 let only_decl =
                                   ((let uu____7248 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7248)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7249 =
                                        let uu____7250 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____7250.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____7249)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7260 =
                                       FStar_List.filter
                                         (fun uu___211_7262  ->
                                            match uu___211_7262 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7263 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7260
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___212_7271  ->
                                             match uu___212_7271 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7272 -> false))
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
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____7278 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____7278
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____7282 =
                                        let uu____7285 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____7285  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7282;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____7287 =
                                        let uu____7288 =
                                          let uu____7292 =
                                            let uu____7294 =
                                              let uu____7295 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right uu____7295
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____7294]  in
                                          ((false, [lb]), uu____7292)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7288
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7287;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____7225 FStar_List.flatten
  
let mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____7330,t,uu____7332,n1,uu____7334) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7337 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____7337 with
             | (formals,uu____7347) ->
                 (match formals with
                  | [] -> []
                  | uu____7361 ->
                      let filter_records uu___213_7369 =
                        match uu___213_7369 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7371,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7378 -> None  in
                      let fv_qual =
                        let uu____7380 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____7380 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____7387 = FStar_Util.first_N n1 formals  in
                      (match uu____7387 with
                       | (uu____7399,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7413 -> []
  
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
                    let uu____7459 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____7459
                    then
                      let uu____7461 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____7461
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____7464 =
                      let uu____7467 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____7467  in
                    let uu____7468 =
                      let uu____7471 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____7471  in
                    let uu____7474 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7464;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7468;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7474
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
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
          let tycon_id uu___214_7510 =
            match uu___214_7510 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7512,uu____7513) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7519,uu____7520,uu____7521) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7527,uu____7528,uu____7529) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7545,uu____7546,uu____7547) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7571) ->
                let uu____7572 =
                  let uu____7573 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7573  in
                FStar_Parser_AST.mk_term uu____7572 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7575 =
                  let uu____7576 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7576  in
                FStar_Parser_AST.mk_term uu____7575 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7578) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
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
              | uu____7599 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7602 =
                     let uu____7603 =
                       let uu____7607 = binder_to_term b  in
                       (out, uu____7607, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____7603  in
                   FStar_Parser_AST.mk_term uu____7602
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___215_7614 =
            match uu___215_7614 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____7643  ->
                       match uu____7643 with
                       | (x,t,uu____7650) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____7654 =
                    let uu____7655 =
                      let uu____7656 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____7656  in
                    FStar_Parser_AST.mk_term uu____7655
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____7654 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____7659 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7671  ->
                          match uu____7671 with
                          | (x,uu____7677,uu____7678) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7659)
            | uu____7705 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___216_7727 =
            match uu___216_7727 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7741 = typars_of_binders _env binders  in
                (match uu____7741 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7769 =
                         let uu____7770 =
                           let uu____7771 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7771  in
                         FStar_Parser_AST.mk_term uu____7770
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7769 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
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
            | uu____7781 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7807 =
              FStar_List.fold_left
                (fun uu____7823  ->
                   fun uu____7824  ->
                     match (uu____7823, uu____7824) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7872 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7872 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7807 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7933 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7933
                | uu____7934 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7939 = desugar_abstract_tc quals env [] tc  in
              (match uu____7939 with
               | (uu____7946,uu____7947,se,uu____7949) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7952,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           let uu____7961 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7961
                           then quals1
                           else
                             ((let uu____7966 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               let uu____7967 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7966 uu____7967);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7971 ->
                               let uu____7972 =
                                 let uu____7975 =
                                   let uu____7976 =
                                     let uu____7984 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7984)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7976
                                    in
                                 FStar_Syntax_Syntax.mk uu____7975  in
                               uu____7972 None se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___241_7993 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___241_7993.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_7993.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___241_7993.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____7995 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____7998 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____7998
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____8008 = typars_of_binders env binders  in
              (match uu____8008 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____8028 =
                           FStar_Util.for_some
                             (fun uu___217_8029  ->
                                match uu___217_8029 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____8030 -> false) quals
                            in
                         if uu____8028
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____8036 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___218_8038  ->
                               match uu___218_8038 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____8039 -> false))
                        in
                     if uu____8036
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____8046 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____8046
                     then
                       let uu____8048 =
                         let uu____8052 =
                           let uu____8053 = unparen t  in
                           uu____8053.FStar_Parser_AST.tm  in
                         match uu____8052 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____8065 =
                               match FStar_List.rev args with
                               | (last_arg,uu____8081)::args_rev ->
                                   let uu____8088 =
                                     let uu____8089 = unparen last_arg  in
                                     uu____8089.FStar_Parser_AST.tm  in
                                   (match uu____8088 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____8104 -> ([], args))
                               | uu____8109 -> ([], args)  in
                             (match uu____8065 with
                              | (cattributes,args1) ->
                                  let uu____8130 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8130))
                         | uu____8136 -> (t, [])  in
                       match uu____8048 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___219_8151  ->
                                     match uu___219_8151 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8152 -> true))
                              in
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
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____8160)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____8173 = tycon_record_as_variant trec  in
              (match uu____8173 with
               | (t,fs) ->
                   let uu____8183 =
                     let uu____8185 =
                       let uu____8186 =
                         let uu____8191 =
                           let uu____8193 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____8193  in
                         (uu____8191, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____8186  in
                     uu____8185 :: quals  in
                   desugar_tycon env d uu____8183 [t])
          | uu____8196::uu____8197 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____8284 = et  in
                match uu____8284 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8398 ->
                         let trec = tc  in
                         let uu____8411 = tycon_record_as_variant trec  in
                         (match uu____8411 with
                          | (t,fs) ->
                              let uu____8442 =
                                let uu____8444 =
                                  let uu____8445 =
                                    let uu____8450 =
                                      let uu____8452 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____8452  in
                                    (uu____8450, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____8445
                                   in
                                uu____8444 :: quals1  in
                              collect_tcs uu____8442 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8498 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8498 with
                          | (env2,uu____8529,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8607 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8607 with
                          | (env2,uu____8638,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8702 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8726 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8726 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___221_8976  ->
                             match uu___221_8976 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____9012,uu____9013);
                                    FStar_Syntax_Syntax.sigrng = uu____9014;
                                    FStar_Syntax_Syntax.sigquals = uu____9015;
                                    FStar_Syntax_Syntax.sigmeta = uu____9016;
                                    FStar_Syntax_Syntax.sigattrs = uu____9017;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____9050 =
                                     typars_of_binders env1 binders  in
                                   match uu____9050 with
                                   | (env2,tpars1) ->
                                       let uu____9067 =
                                         push_tparams env2 tpars1  in
                                       (match uu____9067 with
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
                                 let uu____9086 =
                                   let uu____9097 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____9097)
                                    in
                                 [uu____9086]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____9134);
                                    FStar_Syntax_Syntax.sigrng = uu____9135;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9137;
                                    FStar_Syntax_Syntax.sigattrs = uu____9138;_},constrs,tconstr,quals1)
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
                                 let uu____9191 = push_tparams env1 tpars  in
                                 (match uu____9191 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9230  ->
                                             match uu____9230 with
                                             | (x,uu____9238) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____9243 =
                                        let uu____9258 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9310  ->
                                                  match uu____9310 with
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
                                                        let uu____9343 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____9343
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___220_9349
                                                                 ->
                                                                match uu___220_9349
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9356
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____9363 =
                                                        let uu____9374 =
                                                          let uu____9375 =
                                                            let uu____9376 =
                                                              let uu____9384
                                                                =
                                                                let uu____9387
                                                                  =
                                                                  let uu____9390
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9390
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9387
                                                                 in
                                                              (name, univs1,
                                                                uu____9384,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9376
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9375;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____9374)
                                                         in
                                                      (name, uu____9363)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9258
                                         in
                                      (match uu____9243 with
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
                             | uu____9515 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9580  ->
                             match uu____9580 with
                             | (name_doc,uu____9595,uu____9596) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9635  ->
                             match uu____9635 with
                             | (uu____9646,uu____9647,se) -> se))
                      in
                   let uu____9663 =
                     let uu____9667 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9667 rng
                      in
                   (match uu____9663 with
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
                               (fun uu____9701  ->
                                  match uu____9701 with
                                  | (uu____9713,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9737,tps,k,uu____9740,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____9758 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9767  ->
                                 match uu____9767 with
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
      let uu____9791 =
        FStar_List.fold_left
          (fun uu____9798  ->
             fun b  ->
               match uu____9798 with
               | (env1,binders1) ->
                   let uu____9810 = desugar_binder env1 b  in
                   (match uu____9810 with
                    | (Some a,k) ->
                        let uu____9820 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k)
                           in
                        (match uu____9820 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9830 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____9791 with
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
                let uu____9914 = desugar_binders monad_env eff_binders  in
                match uu____9914 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9927 =
                        let uu____9928 =
                          let uu____9932 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          fst uu____9932  in
                        FStar_List.length uu____9928  in
                      uu____9927 = (Prims.parse_int "1")  in
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
                          (uu____9963,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9965,uu____9966,uu____9967),uu____9968)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9985 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9986 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9992 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9992 mandatory_members)
                        eff_decls
                       in
                    (match uu____9986 with
                     | (mandatory_members_decls,actions) ->
                         let uu____10002 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____10013  ->
                                   fun decl  ->
                                     match uu____10013 with
                                     | (env2,out) ->
                                         let uu____10025 =
                                           desugar_decl env2 decl  in
                                         (match uu____10025 with
                                          | (env3,ses) ->
                                              let uu____10033 =
                                                let uu____10035 =
                                                  FStar_List.hd ses  in
                                                uu____10035 :: out  in
                                              (env3, uu____10033)))
                                (env1, []))
                            in
                         (match uu____10002 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____10063,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10066,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____10067,
                                                                (def,uu____10069)::
                                                                (cps_type,uu____10071)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10072;
                                                             FStar_Parser_AST.level
                                                               = uu____10073;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10100 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____10100 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____10112 =
                                                   let uu____10113 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____10114 =
                                                     let uu____10115 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10115
                                                      in
                                                   let uu____10118 =
                                                     let uu____10119 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10119
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10113;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10114;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10118
                                                   }  in
                                                 (uu____10112, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10123,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10126,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10145 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____10145 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____10157 =
                                                   let uu____10158 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____10159 =
                                                     let uu____10160 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10160
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10158;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10159;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____10157, doc1))
                                        | uu____10164 ->
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let actions1 =
                                FStar_List.map FStar_Pervasives.fst
                                  actions_docs
                                 in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____10183 =
                                  let uu____10184 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10184
                                   in
                                ([], uu____10183)  in
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
                                    let uu____10196 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____10196)  in
                                  let uu____10206 =
                                    let uu____10207 =
                                      let uu____10208 =
                                        let uu____10209 = lookup "repr"  in
                                        snd uu____10209  in
                                      let uu____10214 = lookup "return"  in
                                      let uu____10215 = lookup "bind"  in
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
                                          uu____10208;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10214;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10215;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10207
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10206;
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
                                       (fun uu___222_10218  ->
                                          match uu___222_10218 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10219 -> true
                                          | uu____10220 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____10226 =
                                     let uu____10227 =
                                       let uu____10228 = lookup "return_wp"
                                          in
                                       let uu____10229 = lookup "bind_wp"  in
                                       let uu____10230 =
                                         lookup "if_then_else"  in
                                       let uu____10231 = lookup "ite_wp"  in
                                       let uu____10232 = lookup "stronger"
                                          in
                                       let uu____10233 = lookup "close_wp"
                                          in
                                       let uu____10234 = lookup "assert_p"
                                          in
                                       let uu____10235 = lookup "assume_p"
                                          in
                                       let uu____10236 = lookup "null_wp"  in
                                       let uu____10237 = lookup "trivial"  in
                                       let uu____10238 =
                                         if rr
                                         then
                                           let uu____10239 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10239
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____10248 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____10250 =
                                         if rr then lookup "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____10228;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10229;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10230;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10231;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10232;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10233;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10234;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10235;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10236;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10237;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10238;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10248;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10250;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10227
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10226;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
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
                                        fun uu____10263  ->
                                          match uu____10263 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10272 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10272
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____10274 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____10274
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env)
                                     in
                                  let quals1 =
                                    [FStar_Syntax_Syntax.Assumption;
                                    FStar_Syntax_Syntax.Reflectable mname]
                                     in
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
      (FStar_Ident.lident option ->
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
                let uu____10299 = desugar_binders env1 eff_binders  in
                match uu____10299 with
                | (env2,binders) ->
                    let uu____10310 =
                      let uu____10320 = head_and_args defn  in
                      match uu____10320 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10345 ->
                                let uu____10346 =
                                  let uu____10347 =
                                    let uu____10350 =
                                      let uu____10351 =
                                        let uu____10352 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____10352 " not found"
                                         in
                                      Prims.strcat "Effect " uu____10351  in
                                    (uu____10350,
                                      (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____10347  in
                                raise uu____10346
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____10354 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10370)::args_rev ->
                                let uu____10377 =
                                  let uu____10378 = unparen last_arg  in
                                  uu____10378.FStar_Parser_AST.tm  in
                                (match uu____10377 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10393 -> ([], args))
                            | uu____10398 -> ([], args)  in
                          (match uu____10354 with
                           | (cattributes,args1) ->
                               let uu____10425 = desugar_args env2 args1  in
                               let uu____10430 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____10425, uu____10430))
                       in
                    (match uu____10310 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____10464 =
                           match uu____10464 with
                           | (uu____10471,x) ->
                               let uu____10475 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____10475 with
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
                                          args
                                         in
                                      let uu____10499 =
                                        let uu____10500 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10500
                                         in
                                      ([], uu____10499))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____10504 =
                             let uu____10505 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             snd uu____10505  in
                           let uu____10511 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____10512 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____10513 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____10514 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____10515 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____10516 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____10517 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____10518 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____10519 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____10520 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____10521 =
                             let uu____10522 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             snd uu____10522  in
                           let uu____10528 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____10529 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____10530 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10533 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____10534 =
                                    let uu____10535 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    snd uu____10535  in
                                  let uu____10541 =
                                    let uu____10542 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    snd uu____10542  in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10533;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10534;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10541
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10504;
                             FStar_Syntax_Syntax.ret_wp = uu____10511;
                             FStar_Syntax_Syntax.bind_wp = uu____10512;
                             FStar_Syntax_Syntax.if_then_else = uu____10513;
                             FStar_Syntax_Syntax.ite_wp = uu____10514;
                             FStar_Syntax_Syntax.stronger = uu____10515;
                             FStar_Syntax_Syntax.close_wp = uu____10516;
                             FStar_Syntax_Syntax.assert_p = uu____10517;
                             FStar_Syntax_Syntax.assume_p = uu____10518;
                             FStar_Syntax_Syntax.null_wp = uu____10519;
                             FStar_Syntax_Syntax.trivial = uu____10520;
                             FStar_Syntax_Syntax.repr = uu____10521;
                             FStar_Syntax_Syntax.return_repr = uu____10528;
                             FStar_Syntax_Syntax.bind_repr = uu____10529;
                             FStar_Syntax_Syntax.actions = uu____10530
                           }  in
                         let se =
                           let for_free =
                             let uu____10550 =
                               let uu____10551 =
                                 let uu____10555 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 fst uu____10555  in
                               FStar_List.length uu____10551  in
                             uu____10550 = (Prims.parse_int "1")  in
                           let uu____10576 =
                             let uu____10578 = trans_qual1 (Some mname)  in
                             FStar_List.map uu____10578 quals  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10576;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
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
                                       let uu____10592 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10592
                                        in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____10594 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____10594
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env)
                                in
                             let quals1 =
                               [FStar_Syntax_Syntax.Assumption;
                               FStar_Syntax_Syntax.Reflectable mname]  in
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
      let uu____10608 = desugar_decl_noattrs env d  in
      match uu____10608 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          (FStar_List.iter
             (fun a  ->
                let uu____10620 = FStar_Syntax_Print.term_to_string a  in
                FStar_Util.print1 "Desugared attribute: %s\n" uu____10620)
             attrs1;
           (let uu____10621 =
              FStar_List.map
                (fun sigelt  ->
                   let uu___242_10624 = sigelt  in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___242_10624.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___242_10624.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___242_10624.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___242_10624.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs = attrs1
                   }) sigelts
               in
            (env1, uu____10621)))

and desugar_decl_noattrs :
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
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____10643 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10655 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____10655, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____10676  ->
                 match uu____10676 with | (x,uu____10681) -> x) tcs
             in
          let uu____10684 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d uu____10684 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10696;
                    FStar_Parser_AST.prange = uu____10697;_},uu____10698)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10703;
                    FStar_Parser_AST.prange = uu____10704;_},uu____10705)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10713;
                         FStar_Parser_AST.prange = uu____10714;_},uu____10715);
                    FStar_Parser_AST.prange = uu____10716;_},uu____10717)::[]
                   -> false
               | (p,uu____10726)::[] ->
                   let uu____10731 = is_app_pattern p  in
                   Prims.op_Negation uu____10731
               | uu____10732 -> false)
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
            let uu____10743 =
              let uu____10744 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____10744.FStar_Syntax_Syntax.n  in
            (match uu____10743 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10750) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____10770::uu____10771 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10773 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___223_10777  ->
                               match uu___223_10777 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10779;
                                   FStar_Syntax_Syntax.lbunivs = uu____10780;
                                   FStar_Syntax_Syntax.lbtyp = uu____10781;
                                   FStar_Syntax_Syntax.lbeff = uu____10782;
                                   FStar_Syntax_Syntax.lbdef = uu____10783;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10790;
                                   FStar_Syntax_Syntax.lbtyp = uu____10791;
                                   FStar_Syntax_Syntax.lbeff = uu____10792;
                                   FStar_Syntax_Syntax.lbdef = uu____10793;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____10805 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10811  ->
                             match uu____10811 with
                             | (uu____10814,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____10805
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____10822 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____10822
                   then
                     let uu____10827 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___243_10834 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___244_10835 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___244_10835.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___244_10835.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___243_10834.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___243_10834.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___243_10834.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___243_10834.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((fst lbs), uu____10827)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = []
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____10861 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10865 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10876 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____10865 with
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
                       let uu___245_10892 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___245_10892.FStar_Parser_AST.prange)
                       }
                   | uu____10893 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___246_10897 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___246_10897.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___246_10897.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___246_10897.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____10916 id =
                   match uu____10916 with
                   | (env1,ses) ->
                       let main =
                         let uu____10929 =
                           let uu____10930 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____10930  in
                         FStar_Parser_AST.mk_term uu____10929
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
                       let uu____10958 = desugar_decl env1 id_decl  in
                       (match uu____10958 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____10969 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____10969 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
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
                 (FStar_Syntax_Syntax.Sig_assume (lid, f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____10990 = close_fun env t  in
            desugar_term env uu____10990  in
          let quals1 =
            let uu____10993 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____10993
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____10998 = FStar_List.map (trans_qual1 None) quals1  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10998;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____11006 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____11006 with
           | (t,uu____11014) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Syntax_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Syntax_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____11039 =
              let uu____11043 = FStar_Syntax_Syntax.null_binder t  in
              [uu____11043]  in
            let uu____11044 =
              let uu____11047 =
                let uu____11048 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                fst uu____11048  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____11047
               in
            FStar_Syntax_Util.arrow uu____11039 uu____11044  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Syntax_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
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
            let uu____11092 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____11092 with
            | None  ->
                let uu____11094 =
                  let uu____11095 =
                    let uu____11098 =
                      let uu____11099 =
                        let uu____11100 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____11100 " not found"  in
                      Prims.strcat "Effect name " uu____11099  in
                    (uu____11098, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____11095  in
                raise uu____11094
            | Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____11104 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11126 =
                  let uu____11131 =
                    let uu____11135 = desugar_term env t  in
                    ([], uu____11135)  in
                  Some uu____11131  in
                (uu____11126, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11153 =
                  let uu____11158 =
                    let uu____11162 = desugar_term env wp  in
                    ([], uu____11162)  in
                  Some uu____11158  in
                let uu____11167 =
                  let uu____11172 =
                    let uu____11176 = desugar_term env t  in
                    ([], uu____11176)  in
                  Some uu____11172  in
                (uu____11153, uu____11167)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11190 =
                  let uu____11195 =
                    let uu____11199 = desugar_term env t  in
                    ([], uu____11199)  in
                  Some uu____11195  in
                (None, uu____11190)
             in
          (match uu____11104 with
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
        (fun uu____11252  ->
           fun d  ->
             match uu____11252 with
             | (env1,sigelts) ->
                 let uu____11264 = desugar_decl env1 d  in
                 (match uu____11264 with
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
  FStar_Syntax_Syntax.modul option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (None ,uu____11309) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11312;
               FStar_Syntax_Syntax.exports = uu____11313;
               FStar_Syntax_Syntax.is_interface = uu____11314;_},FStar_Parser_AST.Module
             (current_lid,uu____11316)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11321) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____11323 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11343 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____11343, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11353 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____11353, mname, decls, false)
           in
        match uu____11323 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11371 = desugar_decls env2 decls  in
            (match uu____11371 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____11409 =
            (FStar_Options.interactive ()) &&
              (let uu____11410 =
                 let uu____11411 =
                   let uu____11412 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____11412  in
                 FStar_Util.get_file_extension uu____11411  in
               uu____11410 = "fsti")
             in
          if uu____11409 then as_interface m else m  in
        let uu____11415 = desugar_modul_common curmod env m1  in
        match uu____11415 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11425 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11439 = desugar_modul_common None env m  in
      match uu____11439 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____11450 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____11450
            then
              let uu____11451 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____11451
            else ());
           (let uu____11453 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____11453, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11466 =
        FStar_List.fold_left
          (fun uu____11473  ->
             fun m  ->
               match uu____11473 with
               | (env1,mods) ->
                   let uu____11485 = desugar_modul env1 m  in
                   (match uu____11485 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____11466 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11511 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____11511 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11517 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name
               in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11517
              m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  