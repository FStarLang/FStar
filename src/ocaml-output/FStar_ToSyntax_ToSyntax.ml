open Prims
let desugar_disjunctive_pattern:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
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
let trans_aqual:
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Syntax_Syntax.arg_qualifier option
  =
<<<<<<< HEAD
  fun uu___196_42  ->
    match uu___196_42 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____45 -> None
=======
  fun uu___198_51  ->
    match uu___198_51 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____54 -> None
>>>>>>> origin/guido_tactics
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
<<<<<<< HEAD
      fun uu___197_56  ->
        match uu___197_56 with
=======
      fun uu___199_68  ->
        match uu___199_68 with
>>>>>>> origin/guido_tactics
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
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
<<<<<<< HEAD
  fun uu___198_62  ->
    match uu___198_62 with
=======
  fun uu___200_75  ->
    match uu___200_75 with
>>>>>>> origin/guido_tactics
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
<<<<<<< HEAD
  fun uu___199_69  ->
    match uu___199_69 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____71 -> None
=======
  fun uu___201_83  ->
    match uu___201_83 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____85 -> None
>>>>>>> origin/guido_tactics
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
<<<<<<< HEAD
  | uu____104 -> (t, None)
=======
  | uu____124 -> (t, None)
>>>>>>> origin/guido_tactics
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
<<<<<<< HEAD
            | FStar_Parser_AST.Annotated uu____115 -> true
            | uu____118 -> false))
=======
            | FStar_Parser_AST.Annotated uu____134 -> true
            | uu____137 -> false))
>>>>>>> origin/guido_tactics
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
<<<<<<< HEAD
    | uu____123 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____127 =
      let uu____128 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____128 in
    FStar_Parser_AST.mk_term uu____127 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____132 =
      let uu____133 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____133 in
    FStar_Parser_AST.mk_term uu____132 r FStar_Parser_AST.Kind
=======
    | uu____143 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____148 =
      let uu____149 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____149 in
    FStar_Parser_AST.mk_term uu____148 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____154 =
      let uu____155 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____155 in
    FStar_Parser_AST.mk_term uu____154 r FStar_Parser_AST.Kind
>>>>>>> origin/guido_tactics
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
<<<<<<< HEAD
          let uu____141 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____141 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____145) ->
          let uu____152 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____152 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____156,uu____157) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____160,uu____161) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____164,t1) -> is_comp_type env t1
      | uu____166 -> false
=======
          let uu____165 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____165 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____169) ->
          let uu____176 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____176 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____180,uu____181) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____184,uu____185) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____188,t1) -> is_comp_type env t1
      | uu____190 -> false
>>>>>>> origin/guido_tactics
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
<<<<<<< HEAD
        let uu____176 =
          let uu____178 =
            let uu____179 =
              let uu____182 = FStar_Parser_AST.compile_op n1 s in
              (uu____182, r) in
            FStar_Ident.mk_ident uu____179 in
          [uu____178] in
        FStar_All.pipe_right uu____176 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____215 =
      let uu____216 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____216 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____215 in
  let fallback uu____221 =
=======
        let uu____203 =
          let uu____205 =
            let uu____206 =
              let uu____209 = FStar_Parser_AST.compile_op n1 s in
              (uu____209, r) in
            FStar_Ident.mk_ident uu____206 in
          [uu____205] in
        FStar_All.pipe_right uu____203 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____247 =
      let uu____248 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____248 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____247 in
  let fallback uu____253 =
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____223 = FStar_Options.ml_ish () in
        if uu____223
=======
        let uu____255 = FStar_Options.ml_ish () in
        if uu____255
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | uu____226 -> None in
  let uu____227 =
    let uu____231 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____231 in
  match uu____227 with | Some t -> Some (fst t) | uu____238 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____248 =
=======
    | uu____258 -> None in
  let uu____259 =
    let uu____263 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____263 in
  match uu____259 with | Some t -> Some (fst t) | uu____270 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____281 =
>>>>>>> origin/guido_tactics
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
<<<<<<< HEAD
      uu____248
=======
      uu____281
>>>>>>> origin/guido_tactics
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
<<<<<<< HEAD
      | FStar_Parser_AST.Variable uu____277 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____280 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____280 with | (env1,uu____287) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____289,term) ->
          let uu____291 = free_type_vars env term in (env, uu____291)
      | FStar_Parser_AST.TAnnotated (id,uu____295) ->
          let uu____296 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____296 with | (env1,uu____303) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____306 = free_type_vars env t in (env, uu____306)
=======
      | FStar_Parser_AST.Variable uu____306 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____309 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____309 with | (env1,uu____316) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____318,term) ->
          let uu____320 = free_type_vars env term in (env, uu____320)
      | FStar_Parser_AST.TAnnotated (id,uu____324) ->
          let uu____325 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____325 with | (env1,uu____332) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____335 = free_type_vars env t in (env, uu____335)
>>>>>>> origin/guido_tactics
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
<<<<<<< HEAD
      let uu____311 =
        let uu____312 = unparen t in uu____312.FStar_Parser_AST.tm in
      match uu____311 with
      | FStar_Parser_AST.Labeled uu____314 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____320 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____320 with | None  -> [a] | uu____327 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____331 -> []
      | FStar_Parser_AST.Uvar uu____332 -> []
      | FStar_Parser_AST.Var uu____333 -> []
      | FStar_Parser_AST.Projector uu____334 -> []
      | FStar_Parser_AST.Discrim uu____337 -> []
      | FStar_Parser_AST.Name uu____338 -> []
      | FStar_Parser_AST.Assign (uu____339,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____342) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____346) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____349,t1) -> free_type_vars env t1
=======
      let uu____340 =
        let uu____341 = unparen t in uu____341.FStar_Parser_AST.tm in
      match uu____340 with
      | FStar_Parser_AST.Labeled uu____343 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____349 = FStar_ToSyntax_Env.try_lookup_id env a in
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
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
<<<<<<< HEAD
      | FStar_Parser_AST.Construct (uu____361,ts) ->
          FStar_List.collect
            (fun uu____374  ->
               match uu____374 with | (t1,uu____379) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____380,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____386) ->
          let uu____387 = free_type_vars env t1 in
          let uu____389 = free_type_vars env t2 in
          FStar_List.append uu____387 uu____389
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____393 = free_type_vars_b env b in
          (match uu____393 with
           | (env1,f) ->
               let uu____402 = free_type_vars env1 t1 in
               FStar_List.append f uu____402)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____408 =
            FStar_List.fold_left
              (fun uu____422  ->
                 fun binder  ->
                   match uu____422 with
                   | (env1,free) ->
                       let uu____434 = free_type_vars_b env1 binder in
                       (match uu____434 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____408 with
           | (env1,free) ->
               let uu____452 = free_type_vars env1 body in
               FStar_List.append free uu____452)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____458 =
            FStar_List.fold_left
              (fun uu____472  ->
                 fun binder  ->
                   match uu____472 with
                   | (env1,free) ->
                       let uu____484 = free_type_vars_b env1 binder in
                       (match uu____484 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____458 with
           | (env1,free) ->
               let uu____502 = free_type_vars env1 body in
               FStar_List.append free uu____502)
      | FStar_Parser_AST.Project (t1,uu____505) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____508 -> []
      | FStar_Parser_AST.Let uu____512 -> []
      | FStar_Parser_AST.LetOpen uu____519 -> []
      | FStar_Parser_AST.If uu____522 -> []
      | FStar_Parser_AST.QForall uu____526 -> []
      | FStar_Parser_AST.QExists uu____533 -> []
      | FStar_Parser_AST.Record uu____540 -> []
      | FStar_Parser_AST.Match uu____547 -> []
      | FStar_Parser_AST.TryWith uu____555 -> []
      | FStar_Parser_AST.Bind uu____563 -> []
      | FStar_Parser_AST.Seq uu____567 -> []
=======
      | FStar_Parser_AST.Construct (uu____390,ts) ->
          FStar_List.collect
            (fun uu____400  ->
               match uu____400 with | (t1,uu____405) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____406,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____412) ->
          let uu____413 = free_type_vars env t1 in
          let uu____415 = free_type_vars env t2 in
          FStar_List.append uu____413 uu____415
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____419 = free_type_vars_b env b in
          (match uu____419 with
           | (env1,f) ->
               let uu____428 = free_type_vars env1 t1 in
               FStar_List.append f uu____428)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____434 =
            FStar_List.fold_left
              (fun uu____441  ->
                 fun binder  ->
                   match uu____441 with
                   | (env1,free) ->
                       let uu____453 = free_type_vars_b env1 binder in
                       (match uu____453 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____434 with
           | (env1,free) ->
               let uu____471 = free_type_vars env1 body in
               FStar_List.append free uu____471)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____477 =
            FStar_List.fold_left
              (fun uu____484  ->
                 fun binder  ->
                   match uu____484 with
                   | (env1,free) ->
                       let uu____496 = free_type_vars_b env1 binder in
                       (match uu____496 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____477 with
           | (env1,free) ->
               let uu____514 = free_type_vars env1 body in
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
>>>>>>> origin/guido_tactics
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
<<<<<<< HEAD
      let uu____596 =
        let uu____597 = unparen t1 in uu____597.FStar_Parser_AST.tm in
      match uu____596 with
=======
      let uu____609 =
        let uu____610 = unparen t1 in uu____610.FStar_Parser_AST.tm in
      match uu____609 with
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
<<<<<<< HEAD
      | uu____621 -> (t1, args) in
=======
      | uu____634 -> (t1, args) in
>>>>>>> origin/guido_tactics
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
<<<<<<< HEAD
        let uu____635 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____635 in
=======
        let uu____650 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____650 in
>>>>>>> origin/guido_tactics
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
<<<<<<< HEAD
                   let uu____649 =
                     let uu____650 =
                       let uu____653 = tm_type x.FStar_Ident.idRange in
                       (x, uu____653) in
                     FStar_Parser_AST.TAnnotated uu____650 in
                   FStar_Parser_AST.mk_binder uu____649 x.FStar_Ident.idRange
=======
                   let uu____664 =
                     let uu____665 =
                       let uu____668 = tm_type x.FStar_Ident.idRange in
                       (x, uu____668) in
                     FStar_Parser_AST.TAnnotated uu____665 in
                   FStar_Parser_AST.mk_binder uu____664 x.FStar_Ident.idRange
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____664 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____664 in
=======
        let uu____681 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____681 in
>>>>>>> origin/guido_tactics
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
<<<<<<< HEAD
                   let uu____678 =
                     let uu____679 =
                       let uu____682 = tm_type x.FStar_Ident.idRange in
                       (x, uu____682) in
                     FStar_Parser_AST.TAnnotated uu____679 in
                   FStar_Parser_AST.mk_binder uu____678 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____684 =
             let uu____685 = unparen t in uu____685.FStar_Parser_AST.tm in
           match uu____684 with
           | FStar_Parser_AST.Product uu____686 -> t
           | uu____690 ->
=======
                   let uu____695 =
                     let uu____696 =
                       let uu____699 = tm_type x.FStar_Ident.idRange in
                       (x, uu____699) in
                     FStar_Parser_AST.TAnnotated uu____696 in
                   FStar_Parser_AST.mk_binder uu____695 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____701 =
             let uu____702 = unparen t in uu____702.FStar_Parser_AST.tm in
           match uu____701 with
           | FStar_Parser_AST.Product uu____703 -> t
           | uu____707 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____711 -> (bs, t)
=======
      | uu____730 -> (bs, t)
>>>>>>> origin/guido_tactics
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
<<<<<<< HEAD
    | FStar_Parser_AST.PatTvar (uu____716,uu____717) -> true
    | FStar_Parser_AST.PatVar (uu____720,uu____721) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____725) -> is_var_pattern p1
    | uu____726 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____731) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____732;
           FStar_Parser_AST.prange = uu____733;_},uu____734)
        -> true
    | uu____740 -> false
=======
    | FStar_Parser_AST.PatTvar (uu____736,uu____737) -> true
    | FStar_Parser_AST.PatVar (uu____740,uu____741) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____745) -> is_var_pattern p1
    | uu____746 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____752) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____753;
           FStar_Parser_AST.prange = uu____754;_},uu____755)
        -> true
    | uu____761 -> false
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | uu____744 -> p
=======
    | uu____766 -> p
>>>>>>> origin/guido_tactics
let rec destruct_app_pattern:
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either*
          FStar_Parser_AST.pattern Prims.list* FStar_Parser_AST.term option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
<<<<<<< HEAD
            let uu____770 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____770 with
             | (name,args,uu____787) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____801);
               FStar_Parser_AST.prange = uu____802;_},args)
            when is_top_level1 ->
            let uu____808 =
              let uu____811 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____811 in
            (uu____808, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____817);
               FStar_Parser_AST.prange = uu____818;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____828 -> failwith "Not an app pattern"
=======
            let uu____795 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____795 with
             | (name,args,uu____812) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____826);
               FStar_Parser_AST.prange = uu____827;_},args)
            when is_top_level1 ->
            let uu____833 =
              let uu____836 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____836 in
            (uu____833, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____842);
               FStar_Parser_AST.prange = uu____843;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____853 -> failwith "Not an app pattern"
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | FStar_Parser_AST.PatConst uu____852 -> acc
      | FStar_Parser_AST.PatVar (uu____853,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____855 -> acc
      | FStar_Parser_AST.PatTvar uu____856 -> acc
      | FStar_Parser_AST.PatOp uu____860 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____866) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____872) ->
=======
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
>>>>>>> origin/guido_tactics
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
<<<<<<< HEAD
          let uu____881 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____881
      | FStar_Parser_AST.PatAscribed (pat,uu____886) ->
=======
          let uu____908 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____908
      | FStar_Parser_AST.PatAscribed (pat,uu____913) ->
>>>>>>> origin/guido_tactics
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
<<<<<<< HEAD
           else Prims.parse_int "1") (fun uu____898  -> Prims.parse_int "0") in
=======
           else Prims.parse_int "1") (fun uu____923  -> Prims.parse_int "0") in
>>>>>>> origin/guido_tactics
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | LocalBinder _0 -> true | uu____918 -> false
=======
    match projectee with | LocalBinder _0 -> true | uu____944 -> false
>>>>>>> origin/guido_tactics
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | LetBinder _0 -> true | uu____938 -> false
=======
    match projectee with | LetBinder _0 -> true | uu____966 -> false
>>>>>>> origin/guido_tactics
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
<<<<<<< HEAD
  fun uu___200_956  ->
    match uu___200_956 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____961 -> failwith "Impossible"
=======
  fun uu___202_986  ->
    match uu___202_986 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____991 -> failwith "Impossible"
>>>>>>> origin/guido_tactics
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
<<<<<<< HEAD
      fun uu___201_978  ->
        match uu___201_978 with
        | (None ,k) ->
            let uu____987 = FStar_Syntax_Syntax.null_binder k in
            (uu____987, env)
        | (Some a,k) ->
            let uu____991 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____991 with
             | (env1,a1) ->
                 (((let uu___222_1003 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___222_1003.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___222_1003.FStar_Syntax_Syntax.index);
=======
      fun uu___203_1011  ->
        match uu___203_1011 with
        | (None ,k) ->
            let uu____1020 = FStar_Syntax_Syntax.null_binder k in
            (uu____1020, env)
        | (Some a,k) ->
            let uu____1024 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1024 with
             | (env1,a1) ->
                 (((let uu___224_1035 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___224_1035.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___224_1035.FStar_Syntax_Syntax.index);
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
  fun uu____1016  ->
    match uu____1016 with
=======
  fun uu____1049  ->
    match uu____1049 with
>>>>>>> origin/guido_tactics
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None
let mk_ref_read tm =
  let tm' =
<<<<<<< HEAD
    let uu____1066 =
      let uu____1076 =
        let uu____1077 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1077 in
      let uu____1078 =
        let uu____1084 =
          let uu____1089 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1089) in
        [uu____1084] in
      (uu____1076, uu____1078) in
    FStar_Syntax_Syntax.Tm_app uu____1066 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1123 =
      let uu____1133 =
        let uu____1134 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1134 in
      let uu____1135 =
        let uu____1141 =
          let uu____1146 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1146) in
        [uu____1141] in
      (uu____1133, uu____1135) in
    FStar_Syntax_Syntax.Tm_app uu____1123 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1194 =
      let uu____1204 =
        let uu____1205 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1205 in
      let uu____1206 =
        let uu____1212 =
          let uu____1217 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1217) in
        let uu____1220 =
          let uu____1226 =
            let uu____1231 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1231) in
          [uu____1226] in
        uu____1212 :: uu____1220 in
      (uu____1204, uu____1206) in
    FStar_Syntax_Syntax.Tm_app uu____1194 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___202_1257  ->
    match uu___202_1257 with
=======
    let uu____1098 =
      let uu____1108 =
        let uu____1109 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1109 in
      let uu____1110 =
        let uu____1116 =
          let uu____1121 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1121) in
        [uu____1116] in
      (uu____1108, uu____1110) in
    FStar_Syntax_Syntax.Tm_app uu____1098 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1157 =
      let uu____1167 =
        let uu____1168 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1168 in
      let uu____1169 =
        let uu____1175 =
          let uu____1180 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1180) in
        [uu____1175] in
      (uu____1167, uu____1169) in
    FStar_Syntax_Syntax.Tm_app uu____1157 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1232 =
      let uu____1242 =
        let uu____1243 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1243 in
      let uu____1244 =
        let uu____1250 =
          let uu____1255 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1255) in
        let uu____1258 =
          let uu____1264 =
            let uu____1269 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1269) in
          [uu____1264] in
        uu____1250 :: uu____1258 in
      (uu____1242, uu____1244) in
    FStar_Syntax_Syntax.Tm_app uu____1232 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___204_1296  ->
    match uu___204_1296 with
>>>>>>> origin/guido_tactics
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
<<<<<<< HEAD
    | uu____1258 -> false
=======
    | uu____1297 -> false
>>>>>>> origin/guido_tactics
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
<<<<<<< HEAD
        (let uu____1266 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1266)
=======
        (let uu____1307 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1307)
>>>>>>> origin/guido_tactics
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
<<<<<<< HEAD
    let uu____1277 =
      let uu____1278 = unparen t in uu____1278.FStar_Parser_AST.tm in
    match uu____1277 with
    | FStar_Parser_AST.Wild  ->
        let uu____1281 =
          let uu____1282 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1282 in
        FStar_Util.Inr uu____1281
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1289)) ->
=======
    let uu____1320 =
      let uu____1321 = unparen t in uu____1321.FStar_Parser_AST.tm in
    match uu____1320 with
    | FStar_Parser_AST.Wild  ->
        let uu____1324 =
          let uu____1325 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1325 in
        FStar_Util.Inr uu____1324
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1330)) ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
             let uu____1329 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1329
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1336 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1336
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1343 =
               let uu____1344 =
                 let uu____1347 =
                   let uu____1348 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1348 in
                 (uu____1347, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1344 in
             raise uu____1343)
    | FStar_Parser_AST.App uu____1351 ->
        let rec aux t1 univargs =
          let uu____1370 =
            let uu____1371 = unparen t1 in uu____1371.FStar_Parser_AST.tm in
          match uu____1370 with
          | FStar_Parser_AST.App (t2,targ,uu____1376) ->
=======
             let uu____1369 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1369
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1376 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1376
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1383 =
               let uu____1384 =
                 let uu____1387 =
                   let uu____1388 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1388 in
                 (uu____1387, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1384 in
             raise uu____1383)
    | FStar_Parser_AST.App uu____1391 ->
        let rec aux t1 univargs =
          let uu____1410 =
            let uu____1411 = unparen t1 in uu____1411.FStar_Parser_AST.tm in
          match uu____1410 with
          | FStar_Parser_AST.App (t2,targ,uu____1416) ->
>>>>>>> origin/guido_tactics
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
<<<<<<< HEAD
                  (fun uu___203_1391  ->
                     match uu___203_1391 with
                     | FStar_Util.Inr uu____1394 -> true
                     | uu____1395 -> false) univargs
              then
                let uu____1398 =
                  let uu____1399 =
                    FStar_List.map
                      (fun uu___204_1405  ->
                         match uu___204_1405 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1399 in
                FStar_Util.Inr uu____1398
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___205_1417  ->
                        match uu___205_1417 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1421 -> failwith "impossible")
                     univargs in
                 let uu____1422 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1422)
          | uu____1428 ->
              let uu____1429 =
                let uu____1430 =
                  let uu____1433 =
                    let uu____1434 =
                      let uu____1435 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1435 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1434 in
                  (uu____1433, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1430 in
              raise uu____1429 in
        aux t []
    | uu____1440 ->
        let uu____1441 =
          let uu____1442 =
            let uu____1445 =
              let uu____1446 =
                let uu____1447 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1447 " in universe context" in
              Prims.strcat "Unexpected term " uu____1446 in
            (uu____1445, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1442 in
        raise uu____1441
=======
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
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1436 in
                FStar_Util.Inr uu____1435
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___207_1450  ->
                        match uu___207_1450 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1454 -> failwith "impossible")
                     univargs in
                 let uu____1455 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1455)
          | uu____1459 ->
              let uu____1460 =
                let uu____1461 =
                  let uu____1464 =
                    let uu____1465 =
                      let uu____1466 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1466 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1465 in
                  (uu____1464, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1461 in
              raise uu____1460 in
        aux t []
    | uu____1471 ->
        let uu____1472 =
          let uu____1473 =
            let uu____1476 =
              let uu____1477 =
                let uu____1478 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1478 " in universe context" in
              Prims.strcat "Unexpected term " uu____1477 in
            (uu____1476, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1473 in
        raise uu____1472
>>>>>>> origin/guido_tactics
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
<<<<<<< HEAD
  let uu____1481 = FStar_List.hd fields in
  match uu____1481 with
  | (f,uu____1487) ->
=======
  let uu____1517 = FStar_List.hd fields in
  match uu____1517 with
  | (f,uu____1523) ->
>>>>>>> origin/guido_tactics
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
<<<<<<< HEAD
        let check_field uu____1495 =
          match uu____1495 with
          | (f',uu____1499) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1501 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1501
=======
        let check_field uu____1531 =
          match uu____1531 with
          | (f',uu____1535) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1537 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1537
>>>>>>> origin/guido_tactics
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
<<<<<<< HEAD
        (let uu____1505 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1505);
=======
        (let uu____1541 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1541);
>>>>>>> origin/guido_tactics
        (match () with | () -> record)))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
            | FStar_Syntax_Syntax.Pat_dot_term uu____1665 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1670 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1671 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1673,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1697  ->
                          match uu____1697 with
                          | (p3,uu____1703) ->
                              let uu____1704 = pat_vars p3 in
                              FStar_Util.set_union out uu____1704)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1707) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1708) -> ()
         | (true ,uu____1712) ->
=======
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
                              let uu____1738 = pat_vars p3 in
                              FStar_Util.set_union out uu____1738)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1741) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1742) -> ()
         | (true ,uu____1746) ->
>>>>>>> origin/guido_tactics
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
<<<<<<< HEAD
           let uu____1740 =
=======
           let uu____1774 =
>>>>>>> origin/guido_tactics
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
<<<<<<< HEAD
           match uu____1740 with
           | Some y -> (l, e, y)
           | uu____1749 ->
               let uu____1751 = push_bv_maybe_mut e x in
               (match uu____1751 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
=======
           match uu____1774 with
           | Some y -> (l, e, y)
           | uu____1782 ->
               let uu____1784 = push_bv_maybe_mut e x in
               (match uu____1784 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
>>>>>>> origin/guido_tactics
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
<<<<<<< HEAD
           | FStar_Parser_AST.PatOr uu____1795 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1804 =
                 let uu____1805 =
                   let uu____1806 =
                     let uu____1810 =
                       let uu____1811 =
                         let uu____1814 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1814, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1811 in
                     (uu____1810, None) in
                   FStar_Parser_AST.PatVar uu____1806 in
                 {
                   FStar_Parser_AST.pat = uu____1805;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1804
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1818 = aux loc env1 p2 in
               (match uu____1818 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1839 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1845 = close_fun env1 t in
                            desugar_term env1 uu____1845 in
=======
           | FStar_Parser_AST.PatOr uu____1832 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1842 =
                 let uu____1843 =
                   let uu____1844 =
                     let uu____1848 =
                       let uu____1849 =
                         let uu____1852 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1852, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1849 in
                     (uu____1848, None) in
                   FStar_Parser_AST.PatVar uu____1844 in
                 {
                   FStar_Parser_AST.pat = uu____1843;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1842
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1856 = aux loc env1 p2 in
               (match uu____1856 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1881 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1887 = close_fun env1 t in
                            desugar_term env1 uu____1887 in
>>>>>>> origin/guido_tactics
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
<<<<<<< HEAD
                              | uu____1847 -> true)
                           then
                             (let uu____1848 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1849 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1850 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1848 uu____1849 uu____1850)
                           else ();
                           LocalBinder
                             (((let uu___223_1853 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_1853.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_1853.FStar_Syntax_Syntax.index);
=======
                              | uu____1889 -> true)
                           then
                             (let uu____1890 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1891 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1892 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1890 uu____1891 uu____1892)
                           else ();
                           LocalBinder
                             (((let uu___225_1894 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_1894.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_1894.FStar_Syntax_Syntax.index);
>>>>>>> origin/guido_tactics
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
<<<<<<< HEAD
               let uu____1856 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1856, false)
=======
               let uu____1898 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1898, false)
>>>>>>> origin/guido_tactics
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
<<<<<<< HEAD
               let uu____1863 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1863, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1876 = resolvex loc env1 x in
               (match uu____1876 with
                | (loc1,env2,xbv) ->
                    let uu____1889 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1889, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1902 = resolvex loc env1 x in
               (match uu____1902 with
                | (loc1,env2,xbv) ->
                    let uu____1915 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1915, imp))
=======
               let uu____1908 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1908, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1924 = resolvex loc env1 x in
               (match uu____1924 with
                | (loc1,env2,xbv) ->
                    let uu____1938 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1938, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1954 = resolvex loc env1 x in
               (match uu____1954 with
                | (loc1,env2,xbv) ->
                    let uu____1968 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1968, imp))
>>>>>>> origin/guido_tactics
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
<<<<<<< HEAD
               let uu____1923 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1923, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1936;_},args)
               ->
               let uu____1940 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1967  ->
                        match uu____1967 with
                        | (loc1,env2,args1) ->
                            let uu____1993 = aux loc1 env2 arg in
                            (match uu____1993 with
                             | (loc2,env3,uu____2009,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1940 with
=======
               let uu____1979 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
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
                            let uu____2049 = aux loc1 env2 arg in
                            (match uu____2049 with
                             | (loc2,env3,uu____2067,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2001 with
>>>>>>> origin/guido_tactics
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
<<<<<<< HEAD
                    let uu____2048 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2048, false))
           | FStar_Parser_AST.PatApp uu____2057 ->
=======
                    let uu____2116 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2116, false))
           | FStar_Parser_AST.PatApp uu____2129 ->
>>>>>>> origin/guido_tactics
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
<<<<<<< HEAD
               let uu____2069 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2092  ->
                        match uu____2092 with
                        | (loc1,env2,pats1) ->
                            let uu____2110 = aux loc1 env2 pat in
                            (match uu____2110 with
                             | (loc2,env3,uu____2124,pat1,uu____2126) ->
=======
               let uu____2142 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2156  ->
                        match uu____2156 with
                        | (loc1,env2,pats1) ->
                            let uu____2178 = aux loc1 env2 pat in
                            (match uu____2178 with
                             | (loc2,env3,uu____2194,pat1,uu____2196) ->
>>>>>>> origin/guido_tactics
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2142 with
                | (loc1,env2,pats1) ->
                    let pat =
<<<<<<< HEAD
                      let uu____2150 =
                        let uu____2152 =
                          let uu____2156 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2156 in
                        let uu____2157 =
                          let uu____2158 =
                            let uu____2165 =
=======
                      let uu____2230 =
                        let uu____2233 =
                          let uu____2238 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2238 in
                        let uu____2239 =
                          let uu____2240 =
                            let uu____2248 =
>>>>>>> origin/guido_tactics
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
<<<<<<< HEAD
                            (uu____2165, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2158 in
                        FStar_All.pipe_left uu____2152 uu____2157 in
=======
                            (uu____2248, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2240 in
                        FStar_All.pipe_left uu____2233 uu____2239 in
>>>>>>> origin/guido_tactics
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
<<<<<<< HEAD
                             let uu____2185 =
                               let uu____2186 =
                                 let uu____2193 =
=======
                             let uu____2271 =
                               let uu____2272 =
                                 let uu____2280 =
>>>>>>> origin/guido_tactics
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
<<<<<<< HEAD
                                 (uu____2193, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2186 in
                             FStar_All.pipe_left (pos_r r) uu____2185) pats1
                        uu____2150 in
=======
                                 (uu____2280, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2272 in
                             FStar_All.pipe_left (pos_r r) uu____2271) pats1
                        uu____2230 in
>>>>>>> origin/guido_tactics
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
<<<<<<< HEAD
               let uu____2217 =
                 FStar_List.fold_left
                   (fun uu____2243  ->
                      fun p2  ->
                        match uu____2243 with
                        | (loc1,env2,pats) ->
                            let uu____2270 = aux loc1 env2 p2 in
                            (match uu____2270 with
                             | (loc2,env3,uu____2286,pat,uu____2288) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2217 with
=======
               let uu____2312 =
                 FStar_List.fold_left
                   (fun uu____2329  ->
                      fun p2  ->
                        match uu____2329 with
                        | (loc1,env2,pats) ->
                            let uu____2360 = aux loc1 env2 p2 in
                            (match uu____2360 with
                             | (loc2,env3,uu____2378,pat,uu____2380) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2312 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                    let uu____2345 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2345 with
                     | (constr,uu____2357) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2360 -> failwith "impossible" in
=======
                    let uu____2457 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2457 with
                     | (constr,uu____2470) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2473 -> failwith "impossible" in
>>>>>>> origin/guido_tactics
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
<<<<<<< HEAD
                         let uu____2362 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2362,
=======
                         let uu____2475 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2475,
>>>>>>> origin/guido_tactics
                           false)))
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
<<<<<<< HEAD
                      (fun uu____2401  ->
                         match uu____2401 with
=======
                      (fun uu____2516  ->
                         match uu____2516 with
>>>>>>> origin/guido_tactics
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
<<<<<<< HEAD
                      (fun uu____2420  ->
                         match uu____2420 with
                         | (f,uu____2424) ->
                             let uu____2425 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2440  ->
                                       match uu____2440 with
                                       | (g,uu____2444) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2425 with
=======
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
                                             g.FStar_Ident.idText)) in
                             (match uu____2536 with
>>>>>>> origin/guido_tactics
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
<<<<<<< HEAD
                              | Some (uu____2447,p2) -> p2))) in
               let app =
                 let uu____2452 =
                   let uu____2453 =
                     let uu____2457 =
                       let uu____2458 =
                         let uu____2459 =
=======
                              | Some (uu____2555,p2) -> p2))) in
               let app =
                 let uu____2560 =
                   let uu____2561 =
                     let uu____2565 =
                       let uu____2566 =
                         let uu____2567 =
>>>>>>> origin/guido_tactics
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
<<<<<<< HEAD
                         FStar_Parser_AST.PatName uu____2459 in
                       FStar_Parser_AST.mk_pattern uu____2458
                         p1.FStar_Parser_AST.prange in
                     (uu____2457, args) in
                   FStar_Parser_AST.PatApp uu____2453 in
                 FStar_Parser_AST.mk_pattern uu____2452
                   p1.FStar_Parser_AST.prange in
               let uu____2461 = aux loc env1 app in
               (match uu____2461 with
                | (env2,e,b,p2,uu____2478) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2494 =
                            let uu____2495 =
                              let uu____2502 =
                                let uu___224_2503 = fv in
                                let uu____2504 =
                                  let uu____2506 =
                                    let uu____2507 =
                                      let uu____2511 =
=======
                         FStar_Parser_AST.PatName uu____2567 in
                       FStar_Parser_AST.mk_pattern uu____2566
                         p1.FStar_Parser_AST.prange in
                     (uu____2565, args) in
                   FStar_Parser_AST.PatApp uu____2561 in
                 FStar_Parser_AST.mk_pattern uu____2560
                   p1.FStar_Parser_AST.prange in
               let uu____2569 = aux loc env1 app in
               (match uu____2569 with
                | (env2,e,b,p2,uu____2588) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2610 =
                            let uu____2611 =
                              let uu____2619 =
                                let uu___226_2620 = fv in
                                let uu____2621 =
                                  let uu____2623 =
                                    let uu____2624 =
                                      let uu____2628 =
>>>>>>> origin/guido_tactics
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
<<<<<<< HEAD
                                        uu____2511) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2507 in
                                  Some uu____2506 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___224_2503.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___224_2503.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2504
                                } in
                              (uu____2502, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2495 in
                          FStar_All.pipe_left pos uu____2494
                      | uu____2525 -> p2 in
=======
                                        uu____2628) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2624 in
                                  Some uu____2623 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___226_2620.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___226_2620.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2621
                                } in
                              (uu____2619, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2611 in
                          FStar_All.pipe_left pos uu____2610
                      | uu____2647 -> p2 in
>>>>>>> origin/guido_tactics
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
<<<<<<< HEAD
               let uu____2554 = aux loc env1 p2 in
               (match uu____2554 with
                | (loc1,env2,var,p3,uu____2570) ->
                    let uu____2573 =
                      FStar_List.fold_left
                        (fun uu____2595  ->
                           fun p4  ->
                             match uu____2595 with
                             | (loc2,env3,ps1) ->
                                 let uu____2614 = aux loc2 env3 p4 in
                                 (match uu____2614 with
                                  | (loc3,env4,uu____2628,p5,uu____2630) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2573 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2658 ->
               let uu____2659 = aux loc env1 p1 in
               (match uu____2659 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2682 = aux_maybe_or env p in
         match uu____2682 with
         | (env1,b,pats) ->
             ((let uu____2700 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2700);
=======
               let uu____2680 = aux loc env1 p2 in
               (match uu____2680 with
                | (loc1,env2,var,p3,uu____2698) ->
                    let uu____2703 =
                      FStar_List.fold_left
                        (fun uu____2716  ->
                           fun p4  ->
                             match uu____2716 with
                             | (loc2,env3,ps1) ->
                                 let uu____2739 = aux loc2 env3 p4 in
                                 (match uu____2739 with
                                  | (loc3,env4,uu____2755,p5,uu____2757) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2703 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2798 ->
               let uu____2799 = aux loc env1 p1 in
               (match uu____2799 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2829 = aux_maybe_or env p in
         match uu____2829 with
         | (env1,b,pats) ->
             ((let uu____2850 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2850);
>>>>>>> origin/guido_tactics
              (env1, b, pats)))
and desugar_binding_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
<<<<<<< HEAD
            let uu____2722 =
              let uu____2723 =
                let uu____2726 = FStar_ToSyntax_Env.qualify env x in
                (uu____2726, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2723 in
            (env, uu____2722, []) in
=======
            let uu____2873 =
              let uu____2874 =
                let uu____2877 = FStar_ToSyntax_Env.qualify env x in
                (uu____2877, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2874 in
            (env, uu____2873, []) in
>>>>>>> origin/guido_tactics
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
<<<<<<< HEAD
                let uu____2737 =
                  let uu____2738 =
                    let uu____2741 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2741, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2738 in
                mklet uu____2737
            | FStar_Parser_AST.PatVar (x,uu____2743) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2747);
                   FStar_Parser_AST.prange = uu____2748;_},t)
                ->
                let uu____2752 =
                  let uu____2753 =
                    let uu____2756 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2757 = desugar_term env t in
                    (uu____2756, uu____2757) in
                  LetBinder uu____2753 in
                (env, uu____2752, [])
            | uu____2759 ->
=======
                let uu____2888 =
                  let uu____2889 =
                    let uu____2892 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2892, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2889 in
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
                    let uu____2907 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2908 = desugar_term env t in
                    (uu____2907, uu____2908) in
                  LetBinder uu____2904 in
                (env, uu____2903, [])
            | uu____2910 ->
>>>>>>> origin/guido_tactics
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
<<<<<<< HEAD
            (let uu____2765 = desugar_data_pat env p is_mut in
             match uu____2765 with
=======
            (let uu____2916 = desugar_data_pat env p is_mut in
             match uu____2916 with
>>>>>>> origin/guido_tactics
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
<<<<<<< HEAD
                         uu____2782;
                       FStar_Syntax_Syntax.p = uu____2783;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2786;
                       FStar_Syntax_Syntax.p = uu____2787;_}::[] -> []
                   | uu____2790 -> p1 in
=======
                         uu____2933;
                       FStar_Syntax_Syntax.ty = uu____2934;
                       FStar_Syntax_Syntax.p = uu____2935;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2940;
                       FStar_Syntax_Syntax.ty = uu____2941;
                       FStar_Syntax_Syntax.p = uu____2942;_}::[] -> []
                   | uu____2947 -> p1 in
>>>>>>> origin/guido_tactics
                 (env1, binder, p2))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat Prims.list)
  =
<<<<<<< HEAD
  fun uu____2795  ->
    fun env  ->
      fun pat  ->
        let uu____2798 = desugar_data_pat env pat false in
        match uu____2798 with | (env1,uu____2807,pat1) -> (env1, pat1)
=======
  fun uu____2952  ->
    fun env  ->
      fun pat  ->
        let uu____2955 = desugar_data_pat env pat false in
        match uu____2955 with | (env1,uu____2964,pat1) -> (env1, pat1)
>>>>>>> origin/guido_tactics
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat Prims.list)
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
      (FStar_Const.signedness* FStar_Const.width) ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
<<<<<<< HEAD
      fun uu____2822  ->
        fun range  ->
          match uu____2822 with
          | (signedness,width) ->
              let uu____2830 = FStar_Const.bounds signedness width in
              (match uu____2830 with
               | (lower,upper) ->
                   let value =
                     let uu____2838 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2838 in
=======
      fun uu____2979  ->
        fun range  ->
          match uu____2979 with
          | (signedness,width) ->
              let uu____2987 = FStar_Const.bounds signedness width in
              (match uu____2987 with
               | (lower,upper) ->
                   let value =
                     let uu____2995 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2995 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                   ((let uu____2841 =
                       (let uu____2844 = FStar_Options.lax () in
                        Prims.op_Negation uu____2844) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____2841
                     then
                       let uu____2845 =
                         let uu____2846 =
                           let uu____2849 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2849, range) in
                         FStar_Errors.Error uu____2846 in
                       raise uu____2845
                     else ());
=======
                   (if
                      Prims.op_Negation
                        ((lower <= value) && (value <= upper))
                    then
                      (let uu____2998 =
                         let uu____2999 =
                           let uu____3002 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____3002, range) in
                         FStar_Errors.Error uu____2999 in
                       raise uu____2998)
                    else ();
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                       let uu____2857 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2857 with
                       | Some (intro_term,uu____2864) ->
=======
                       let uu____3010 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____3010 with
                       | Some (intro_term,uu____3017) ->
>>>>>>> origin/guido_tactics
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
<<<<<<< HEAD
                                  let uu____2872 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2872 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___225_2873 = intro_term in
=======
                                  let uu____3025 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____3025 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___227_3026 = intro_term in
>>>>>>> origin/guido_tactics
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
<<<<<<< HEAD
                                    (uu___225_2873.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___225_2873.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___225_2873.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2878 ->
=======
                                    (uu___227_3026.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___227_3026.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___227_3026.FStar_Syntax_Syntax.vars)
                                }
                            | uu____3031 ->
>>>>>>> origin/guido_tactics
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
<<<<<<< HEAD
                           let uu____2883 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2883 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int (repr, None))) None range in
                     let uu____2898 =
                       let uu____2901 =
                         let uu____2902 =
                           let uu____2912 =
                             let uu____2918 =
                               let uu____2923 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2923) in
                             [uu____2918] in
                           (lid1, uu____2912) in
                         FStar_Syntax_Syntax.Tm_app uu____2902 in
                       FStar_Syntax_Syntax.mk uu____2901 in
                     uu____2898 None range)))
=======
                           let uu____3036 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____3036 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____3055 =
                       let uu____3058 =
                         let uu____3059 =
                           let uu____3069 =
                             let uu____3075 =
                               let uu____3080 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____3080) in
                             [uu____3075] in
                           (lid1, uu____3069) in
                         FStar_Syntax_Syntax.Tm_app uu____3059 in
                       FStar_Syntax_Syntax.mk uu____3058 in
                     uu____3055 None range)))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            let uu____2960 =
=======
            let uu____3117 =
>>>>>>> origin/guido_tactics
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
<<<<<<< HEAD
            match uu____2960 with
=======
            match uu____3117 with
>>>>>>> origin/guido_tactics
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
<<<<<<< HEAD
                  let uu____2971 =
                    let uu____2972 =
                      let uu____2977 = mk_ref_read tm1 in
                      (uu____2977,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2972 in
                  FStar_All.pipe_left mk1 uu____2971
=======
                  let uu____3135 =
                    let uu____3136 =
                      let uu____3141 = mk_ref_read tm1 in
                      (uu____3141,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3136 in
                  FStar_All.pipe_left mk1 uu____3135
>>>>>>> origin/guido_tactics
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
<<<<<<< HEAD
        let uu____2991 =
          let uu____2992 = unparen t in uu____2992.FStar_Parser_AST.tm in
        match uu____2991 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2993; FStar_Ident.ident = uu____2994;
              FStar_Ident.nsstr = uu____2995; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2997 ->
            let uu____2998 =
              let uu____2999 =
                let uu____3002 =
                  let uu____3003 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3003 in
                (uu____3002, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2999 in
            raise uu____2998 in
=======
        let uu____3155 =
          let uu____3156 = unparen t in uu____3156.FStar_Parser_AST.tm in
        match uu____3155 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3157; FStar_Ident.ident = uu____3158;
              FStar_Ident.nsstr = uu____3159; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3161 ->
            let uu____3162 =
              let uu____3163 =
                let uu____3166 =
                  let uu____3167 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3167 in
                (uu____3166, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3163 in
            raise uu____3162 in
>>>>>>> origin/guido_tactics
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e = FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range in
        let setpos e =
<<<<<<< HEAD
          let uu___226_3027 = e in
          {
            FStar_Syntax_Syntax.n = (uu___226_3027.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___226_3027.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___226_3027.FStar_Syntax_Syntax.vars)
          } in
        let uu____3034 =
          let uu____3035 = unparen top in uu____3035.FStar_Parser_AST.tm in
        match uu____3034 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3036 -> desugar_formula env top
=======
          let uu___228_3195 = e in
          {
            FStar_Syntax_Syntax.n = (uu___228_3195.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___228_3195.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___228_3195.FStar_Syntax_Syntax.vars)
          } in
        let uu____3202 =
          let uu____3203 = unparen top in uu____3203.FStar_Parser_AST.tm in
        match uu____3202 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3204 -> desugar_formula env top
>>>>>>> origin/guido_tactics
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
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
<<<<<<< HEAD
        | FStar_Parser_AST.Op (op_star,uu____3068::uu____3069::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3072 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3072 FStar_Option.isNone)
=======
        | FStar_Parser_AST.Op (op_star,uu____3236::uu____3237::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3239 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3239 FStar_Option.isNone)
>>>>>>> origin/guido_tactics
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
<<<<<<< HEAD
                     FStar_Ident.idRange = uu____3081;_},t1::t2::[])
                  ->
                  let uu____3085 = flatten1 t1 in
                  FStar_List.append uu____3085 [t2]
              | uu____3087 -> [t] in
            let targs =
              let uu____3090 =
                let uu____3092 = unparen top in flatten1 uu____3092 in
              FStar_All.pipe_right uu____3090
                (FStar_List.map
                   (fun t  ->
                      let uu____3098 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3098)) in
            let uu____3099 =
              let uu____3102 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3102 in
            (match uu____3099 with
             | (tup,uu____3109) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3112 =
              let uu____3115 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3115 in
            FStar_All.pipe_left setpos uu____3112
=======
                     FStar_Ident.idRange = uu____3248;_},t1::t2::[])
                  ->
                  let uu____3252 = flatten1 t1 in
                  FStar_List.append uu____3252 [t2]
              | uu____3254 -> [t] in
            let targs =
              let uu____3257 =
                let uu____3259 = unparen top in flatten1 uu____3259 in
              FStar_All.pipe_right uu____3257
                (FStar_List.map
                   (fun t  ->
                      let uu____3263 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3263)) in
            let uu____3264 =
              let uu____3267 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3267 in
            (match uu____3264 with
             | (tup,uu____3277) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3280 =
              let uu____3283 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3283 in
            FStar_All.pipe_left setpos uu____3280
>>>>>>> origin/guido_tactics
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
<<<<<<< HEAD
            let uu____3129 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3129 with
=======
            let uu____3297 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3297 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                             let uu____3153 = desugar_term env t in
                             (uu____3153, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3162)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3170 =
              let uu___227_3171 = top in
              let uu____3172 =
                let uu____3173 =
                  let uu____3177 =
                    let uu___228_3178 = top in
                    let uu____3179 =
                      let uu____3180 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3180 in
                    {
                      FStar_Parser_AST.tm = uu____3179;
                      FStar_Parser_AST.range =
                        (uu___228_3178.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___228_3178.FStar_Parser_AST.level)
                    } in
                  (uu____3177, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3173 in
              {
                FStar_Parser_AST.tm = uu____3172;
                FStar_Parser_AST.range =
                  (uu___227_3171.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___227_3171.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3170
        | FStar_Parser_AST.Construct (n1,(a,uu____3183)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3191 =
              let uu___229_3192 = top in
              let uu____3193 =
                let uu____3194 =
                  let uu____3198 =
                    let uu___230_3199 = top in
                    let uu____3200 =
                      let uu____3201 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3201 in
                    {
                      FStar_Parser_AST.tm = uu____3200;
                      FStar_Parser_AST.range =
                        (uu___230_3199.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3199.FStar_Parser_AST.level)
                    } in
                  (uu____3198, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3194 in
              {
                FStar_Parser_AST.tm = uu____3193;
                FStar_Parser_AST.range =
                  (uu___229_3192.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3192.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3191
        | FStar_Parser_AST.Construct (n1,(a,uu____3204)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3212 =
              let uu___231_3213 = top in
              let uu____3214 =
                let uu____3215 =
                  let uu____3219 =
                    let uu___232_3220 = top in
                    let uu____3221 =
                      let uu____3222 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3222 in
                    {
                      FStar_Parser_AST.tm = uu____3221;
                      FStar_Parser_AST.range =
                        (uu___232_3220.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3220.FStar_Parser_AST.level)
                    } in
                  (uu____3219, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3215 in
              {
                FStar_Parser_AST.tm = uu____3214;
                FStar_Parser_AST.range =
                  (uu___231_3213.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3213.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3212
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3223; FStar_Ident.ident = uu____3224;
              FStar_Ident.nsstr = uu____3225; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3227; FStar_Ident.ident = uu____3228;
              FStar_Ident.nsstr = uu____3229; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3231; FStar_Ident.ident = uu____3232;
               FStar_Ident.nsstr = uu____3233; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3243 =
              let uu____3244 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3244 in
            mk1 uu____3243
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3245; FStar_Ident.ident = uu____3246;
              FStar_Ident.nsstr = uu____3247; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3249; FStar_Ident.ident = uu____3250;
              FStar_Ident.nsstr = uu____3251; FStar_Ident.str = "True";_}
=======
                             let uu____3324 = desugar_term env t in
                             (uu____3324, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3333)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3341 =
              let uu___229_3342 = top in
              let uu____3343 =
                let uu____3344 =
                  let uu____3348 =
                    let uu___230_3349 = top in
                    let uu____3350 =
                      let uu____3351 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3351 in
                    {
                      FStar_Parser_AST.tm = uu____3350;
                      FStar_Parser_AST.range =
                        (uu___230_3349.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3349.FStar_Parser_AST.level)
                    } in
                  (uu____3348, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3344 in
              {
                FStar_Parser_AST.tm = uu____3343;
                FStar_Parser_AST.range =
                  (uu___229_3342.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3342.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3341
        | FStar_Parser_AST.Construct (n1,(a,uu____3354)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3362 =
              let uu___231_3363 = top in
              let uu____3364 =
                let uu____3365 =
                  let uu____3369 =
                    let uu___232_3370 = top in
                    let uu____3371 =
                      let uu____3372 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3372 in
                    {
                      FStar_Parser_AST.tm = uu____3371;
                      FStar_Parser_AST.range =
                        (uu___232_3370.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3370.FStar_Parser_AST.level)
                    } in
                  (uu____3369, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3365 in
              {
                FStar_Parser_AST.tm = uu____3364;
                FStar_Parser_AST.range =
                  (uu___231_3363.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3363.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3362
        | FStar_Parser_AST.Construct (n1,(a,uu____3375)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3383 =
              let uu___233_3384 = top in
              let uu____3385 =
                let uu____3386 =
                  let uu____3390 =
                    let uu___234_3391 = top in
                    let uu____3392 =
                      let uu____3393 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3393 in
                    {
                      FStar_Parser_AST.tm = uu____3392;
                      FStar_Parser_AST.range =
                        (uu___234_3391.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3391.FStar_Parser_AST.level)
                    } in
                  (uu____3390, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3386 in
              {
                FStar_Parser_AST.tm = uu____3385;
                FStar_Parser_AST.range =
                  (uu___233_3384.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3384.FStar_Parser_AST.level)
              } in
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
              let uu____3415 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3415 in
            mk1 uu____3414
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3416; FStar_Ident.ident = uu____3417;
              FStar_Ident.nsstr = uu____3418; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3420; FStar_Ident.ident = uu____3421;
              FStar_Ident.nsstr = uu____3422; FStar_Ident.str = "True";_}
>>>>>>> origin/guido_tactics
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
<<<<<<< HEAD
            { FStar_Ident.ns = uu____3253; FStar_Ident.ident = uu____3254;
              FStar_Ident.nsstr = uu____3255; FStar_Ident.str = "False";_}
=======
            { FStar_Ident.ns = uu____3424; FStar_Ident.ident = uu____3425;
              FStar_Ident.nsstr = uu____3426; FStar_Ident.str = "False";_}
>>>>>>> origin/guido_tactics
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
<<<<<<< HEAD
                        FStar_Ident.idRange = uu____3259;_})
=======
                        FStar_Ident.idRange = uu____3430;_})
>>>>>>> origin/guido_tactics
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
<<<<<<< HEAD
             (let uu____3261 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3261 with
=======
             (let uu____3432 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3432 with
>>>>>>> origin/guido_tactics
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
<<<<<<< HEAD
                  let uu____3265 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3265))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3269 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3269 with
=======
                  let uu____3436 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3436))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3440 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3440 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                let uu____3289 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3289 with
                | Some uu____3294 -> Some (true, l)
                | None  ->
                    let uu____3297 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3297 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3305 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3313 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3313
              | uu____3314 ->
                  let uu____3318 =
                    let uu____3319 =
                      let uu____3322 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3322, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3319 in
                  raise uu____3318))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3325 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3325 with
              | None  ->
                  let uu____3327 =
                    let uu____3328 =
                      let uu____3331 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3331, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3328 in
                  raise uu____3327
              | uu____3332 ->
=======
                let uu____3460 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3460 with
                | Some uu____3465 -> Some (true, l)
                | None  ->
                    let uu____3468 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3468 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3476 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3484 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3484
              | uu____3485 ->
                  let uu____3489 =
                    let uu____3490 =
                      let uu____3493 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3493, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3490 in
                  raise uu____3489))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3496 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3496 with
              | None  ->
                  let uu____3498 =
                    let uu____3499 =
                      let uu____3502 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3502, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3499 in
                  raise uu____3498
              | uu____3503 ->
>>>>>>> origin/guido_tactics
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
<<<<<<< HEAD
             (let uu____3344 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3344 with
              | Some head1 ->
                  let uu____3347 =
                    let uu____3352 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3352, true) in
                  (match uu____3347 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3365 ->
                            let uu____3369 =
                              FStar_Util.take
                                (fun uu____3383  ->
                                   match uu____3383 with
                                   | (uu____3386,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3369 with
=======
             (let uu____3515 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3515 with
              | Some head1 ->
                  let uu____3518 =
                    let uu____3523 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3523, true) in
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
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3540 with
>>>>>>> origin/guido_tactics
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
<<<<<<< HEAD
                                     (fun uu____3424  ->
                                        match uu____3424 with
=======
                                     (fun uu____3587  ->
                                        match uu____3587 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                    let uu____3456 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3456 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3458 ->
=======
                    let uu____3619 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3619 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3621 ->
>>>>>>> origin/guido_tactics
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
<<<<<<< HEAD
            let uu____3463 =
              FStar_List.fold_left
                (fun uu____3492  ->
                   fun b  ->
                     match uu____3492 with
                     | (env1,tparams,typs) ->
                         let uu____3523 = desugar_binder env1 b in
                         (match uu____3523 with
                          | (xopt,t1) ->
                              let uu____3539 =
                                match xopt with
                                | None  ->
                                    let uu____3544 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3544)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3539 with
                               | (env2,x) ->
                                   let uu____3556 =
                                     let uu____3558 =
                                       let uu____3560 =
                                         let uu____3561 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3561 in
                                       [uu____3560] in
                                     FStar_List.append typs uu____3558 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___233_3575 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___233_3575.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___233_3575.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3556))))
=======
            let uu____3626 =
              FStar_List.fold_left
                (fun uu____3643  ->
                   fun b  ->
                     match uu____3643 with
                     | (env1,tparams,typs) ->
                         let uu____3674 = desugar_binder env1 b in
                         (match uu____3674 with
                          | (xopt,t1) ->
                              let uu____3690 =
                                match xopt with
                                | None  ->
                                    let uu____3695 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3695)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3690 with
                               | (env2,x) ->
                                   let uu____3707 =
                                     let uu____3709 =
                                       let uu____3711 =
                                         let uu____3712 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3712 in
                                       [uu____3711] in
                                     FStar_List.append typs uu____3709 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___235_3725 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___235_3725.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___235_3725.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3707))))
>>>>>>> origin/guido_tactics
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
<<<<<<< HEAD
            (match uu____3463 with
             | (env1,uu____3588,targs) ->
                 let uu____3600 =
                   let uu____3603 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3603 in
                 (match uu____3600 with
                  | (tup,uu____3610) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3618 = uncurry binders t in
            (match uu____3618 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___206_3641 =
                   match uu___206_3641 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3651 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3651
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3667 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3667 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3678 = desugar_binder env b in
            (match uu____3678 with
             | (None ,uu____3682) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3688 = as_binder env None b1 in
                 (match uu____3688 with
                  | ((x,uu____3692),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3697 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3697))
=======
            (match uu____3626 with
             | (env1,uu____3738,targs) ->
                 let uu____3750 =
                   let uu____3753 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3753 in
                 (match uu____3750 with
                  | (tup,uu____3763) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3771 = uncurry binders t in
            (match uu____3771 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___208_3794 =
                   match uu___208_3794 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3804 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3804
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3820 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3820 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3831 = desugar_binder env b in
            (match uu____3831 with
             | (None ,uu____3835) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3841 = as_binder env None b1 in
                 (match uu____3841 with
                  | ((x,uu____3845),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3850 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3850))
>>>>>>> origin/guido_tactics
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
<<<<<<< HEAD
            let uu____3712 =
              FStar_List.fold_left
                (fun uu____3726  ->
                   fun pat  ->
                     match uu____3726 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3741,t) ->
                              let uu____3743 =
                                let uu____3745 = free_type_vars env1 t in
                                FStar_List.append uu____3745 ftvs in
                              (env1, uu____3743)
                          | uu____3748 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3712 with
             | (uu____3751,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3759 =
=======
            let uu____3865 =
              FStar_List.fold_left
                (fun uu____3872  ->
                   fun pat  ->
                     match uu____3872 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3887,t) ->
                              let uu____3889 =
                                let uu____3891 = free_type_vars env1 t in
                                FStar_List.append uu____3891 ftvs in
                              (env1, uu____3889)
                          | uu____3894 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3865 with
             | (uu____3897,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3905 =
>>>>>>> origin/guido_tactics
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
<<<<<<< HEAD
                   FStar_List.append uu____3759 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___207_3789 =
                   match uu___207_3789 with
=======
                   FStar_List.append uu____3905 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___209_3934 =
                   match uu___209_3934 with
>>>>>>> origin/guido_tactics
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
<<<<<<< HEAD
                               let uu____3818 =
                                 let uu____3819 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3819
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3818 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc, [(pat, None, body2)])) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3857 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3857
                   | p::rest ->
                       let uu____3865 = desugar_binding_pat env1 p in
                       (match uu____3865 with
=======
                               let uu____3963 =
                                 let uu____3964 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3964
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3963 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____4006 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____4006
                   | p::rest ->
                       let uu____4014 = desugar_binding_pat env1 p in
                       (match uu____4014 with
>>>>>>> origin/guido_tactics
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
<<<<<<< HEAD
                              | uu____3881 ->
=======
                              | uu____4030 ->
>>>>>>> origin/guido_tactics
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
<<<<<<< HEAD
                            let uu____3884 =
                              match b with
                              | LetBinder uu____3903 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3934) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3957 =
                                          let uu____3960 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3960, p1) in
                                        Some uu____3957
=======
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
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____4109, p1) in
                                        Some uu____4106
>>>>>>> origin/guido_tactics
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
<<<<<<< HEAD
                                            uu____3985,uu____3986) ->
                                             let tup2 =
                                               let uu____3988 =
=======
                                            uu____4134,uu____4135) ->
                                             let tup2 =
                                               let uu____4137 =
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
<<<<<<< HEAD
                                                 uu____3988
=======
                                                 uu____4137
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
<<<<<<< HEAD
                                               let uu____3992 =
                                                 let uu____3995 =
                                                   let uu____3996 =
                                                     let uu____4006 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4009 =
                                                       let uu____4011 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4012 =
                                                         let uu____4014 =
                                                           let uu____4015 =
=======
                                               let uu____4141 =
                                                 let uu____4144 =
                                                   let uu____4145 =
                                                     let uu____4155 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4158 =
                                                       let uu____4160 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4161 =
                                                         let uu____4163 =
                                                           let uu____4164 =
>>>>>>> origin/guido_tactics
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                             uu____4015 in
                                                         [uu____4014] in
                                                       uu____4011 ::
                                                         uu____4012 in
                                                     (uu____4006, uu____4009) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3996 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3995 in
                                               uu____3992 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4029 =
=======
                                                             uu____4164 in
                                                         [uu____4163] in
                                                       uu____4160 ::
                                                         uu____4161 in
                                                     (uu____4155, uu____4158) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4145 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4144 in
                                               uu____4141 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4179 =
>>>>>>> origin/guido_tactics
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
<<<<<<< HEAD
                                                 uu____4029 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4047,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4049,pats)) ->
                                             let tupn =
                                               let uu____4074 =
=======
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4179 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4199,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4201,pats)) ->
                                             let tupn =
                                               let uu____4228 =
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
<<<<<<< HEAD
                                                 uu____4074
=======
                                                 uu____4228
>>>>>>> origin/guido_tactics
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
<<<<<<< HEAD
                                               let uu____4084 =
                                                 let uu____4085 =
                                                   let uu____4095 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4098 =
                                                     let uu____4104 =
                                                       let uu____4110 =
                                                         let uu____4111 =
=======
                                               let uu____4240 =
                                                 let uu____4241 =
                                                   let uu____4251 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4254 =
                                                     let uu____4260 =
                                                       let uu____4266 =
                                                         let uu____4267 =
>>>>>>> origin/guido_tactics
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
<<<<<<< HEAD
                                                           uu____4111 in
                                                       [uu____4110] in
                                                     FStar_List.append args
                                                       uu____4104 in
                                                   (uu____4095, uu____4098) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4085 in
                                               mk1 uu____4084 in
                                             let p2 =
                                               let uu____4125 =
=======
                                                           uu____4267 in
                                                       [uu____4266] in
                                                     FStar_List.append args
                                                       uu____4260 in
                                                   (uu____4251, uu____4254) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4241 in
                                               mk1 uu____4240 in
                                             let p2 =
                                               let uu____4282 =
>>>>>>> origin/guido_tactics
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
<<<<<<< HEAD
                                                 uu____4125 in
                                             Some (sc1, p2)
                                         | uu____4145 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3884 with
=======
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4282 in
                                             Some (sc1, p2)
                                         | uu____4306 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____4033 with
>>>>>>> origin/guido_tactics
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
<<<<<<< HEAD
            (uu____4186,uu____4187,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4199 =
                let uu____4200 = unparen e in uu____4200.FStar_Parser_AST.tm in
              match uu____4199 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4206 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4209 ->
            let rec aux args e =
              let uu____4230 =
                let uu____4231 = unparen e in uu____4231.FStar_Parser_AST.tm in
              match uu____4230 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4241 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4241 in
                  aux (arg :: args) e1
              | uu____4248 ->
=======
            (uu____4347,uu____4348,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4360 =
                let uu____4361 = unparen e in uu____4361.FStar_Parser_AST.tm in
              match uu____4360 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4367 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
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
                let uu____4376 = unparen top in
                uu____4376.FStar_Parser_AST.tm in
              match uu____4375 with
              | FStar_Parser_AST.App (l,uu____4378,uu____4379) -> l
              | uu____4380 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____4382 =
                let uu____4383 =
                  let uu____4387 =
                    let uu____4388 =
                      let uu____4389 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4389 in
                    FStar_Parser_AST.mk_term uu____4388
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____4390 =
                    let uu____4391 =
                      let uu____4392 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4392 in
                    FStar_Parser_AST.mk_term uu____4391
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____4387, uu____4390, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4383 in
              FStar_Parser_AST.mk_term uu____4382 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type, None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term env t'
        | FStar_Parser_AST.App uu____4395 ->
            let rec aux args e =
              let uu____4416 =
                let uu____4417 = unparen e in uu____4417.FStar_Parser_AST.tm in
              match uu____4416 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4427 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4427 in
                  aux (arg :: args) e1
              | uu____4434 ->
>>>>>>> origin/guido_tactics
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (x, None))
                x.FStar_Ident.idRange in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind1 =
<<<<<<< HEAD
              let uu____4265 =
                let uu____4266 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4266 in
              FStar_Parser_AST.mk_term uu____4265 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4267 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4267
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4270 =
              let uu____4271 =
                let uu____4276 =
=======
              let uu____4451 =
                let uu____4452 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4452 in
              FStar_Parser_AST.mk_term uu____4451 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4453 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4453
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4456 =
              let uu____4457 =
                let uu____4462 =
>>>>>>> origin/guido_tactics
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
<<<<<<< HEAD
                (uu____4276,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4271 in
            mk1 uu____4270
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4287 =
              let uu____4292 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4292 then desugar_typ else desugar_term in
            uu____4287 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4317 =
=======
                (uu____4462,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4457 in
            mk1 uu____4456
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4473 =
              let uu____4478 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4478 then desugar_typ else desugar_term in
            uu____4473 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4503 =
>>>>>>> origin/guido_tactics
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
<<<<<<< HEAD
                     (fun uu____4364  ->
                        match uu____4364 with
                        | (p,def) ->
                            let uu____4378 = is_app_pattern p in
                            if uu____4378
                            then
                              let uu____4388 =
                                destruct_app_pattern env top_level p in
                              (uu____4388, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4417 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4417, def1)
                               | uu____4432 ->
=======
                     (fun uu____4545  ->
                        match uu____4545 with
                        | (p,def) ->
                            let uu____4559 = is_app_pattern p in
                            if uu____4559
                            then
                              let uu____4569 =
                                destruct_app_pattern env top_level p in
                              (uu____4569, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4598 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4598, def1)
                               | uu____4613 ->
>>>>>>> origin/guido_tactics
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
<<<<<<< HEAD
                                             (id,uu____4446);
                                           FStar_Parser_AST.prange =
                                             uu____4447;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4460 =
                                            let uu____4468 =
                                              let uu____4471 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4471 in
                                            (uu____4468, [], (Some t)) in
                                          (uu____4460, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4496)
                                        ->
                                        if top_level
                                        then
                                          let uu____4508 =
                                            let uu____4516 =
                                              let uu____4519 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4519 in
                                            (uu____4516, [], None) in
                                          (uu____4508, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4543 ->
=======
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
                                                  env id in
                                              FStar_Util.Inr uu____4652 in
                                            (uu____4649, [], (Some t)) in
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
                                                  env id in
                                              FStar_Util.Inr uu____4700 in
                                            (uu____4697, [], None) in
                                          (uu____4689, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4724 ->
>>>>>>> origin/guido_tactics
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
<<<<<<< HEAD
              let uu____4553 =
                FStar_List.fold_left
                  (fun uu____4590  ->
                     fun uu____4591  ->
                       match (uu____4590, uu____4591) with
                       | ((env1,fnames,rec_bindings),((f,uu____4635,uu____4636),uu____4637))
                           ->
                           let uu____4677 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4691 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4691 with
                                  | (env2,xx) ->
                                      let uu____4702 =
                                        let uu____4704 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4704 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4702))
                             | FStar_Util.Inr l ->
                                 let uu____4709 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4709, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4677 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4553 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4782 =
                    match uu____4782 with
                    | ((uu____4794,args,result_t),def) ->
=======
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
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4859 with
                                  | (env2,xx) ->
                                      let uu____4870 =
                                        let uu____4872 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4872 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4870))
                             | FStar_Util.Inr l ->
                                 let uu____4877 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4877, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4845 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4734 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4950 =
                    match uu____4950 with
                    | ((uu____4962,args,result_t),def) ->
>>>>>>> origin/guido_tactics
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
<<<<<<< HEAD
                                let uu____4820 = is_comp_type env1 t in
                                if uu____4820
                                then
                                  ((let uu____4822 =
=======
                                let uu____4988 = is_comp_type env1 t in
                                if uu____4988
                                then
                                  ((let uu____4990 =
>>>>>>> origin/guido_tactics
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4995 =
                                                is_var_pattern x in
<<<<<<< HEAD
                                              Prims.op_Negation uu____4829)) in
                                    match uu____4822 with
=======
                                              Prims.op_Negation uu____4995)) in
                                    match uu____4990 with
>>>>>>> origin/guido_tactics
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
<<<<<<< HEAD
                                  (let uu____4832 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4834 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4834))
=======
                                  (let uu____4998 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4999 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4999))
>>>>>>> origin/guido_tactics
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
<<<<<<< HEAD
                                   if uu____4832
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4839 =
=======
                                   if uu____4998
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____5006 =
>>>>>>> origin/guido_tactics
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
<<<<<<< HEAD
                                uu____4839 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4842 ->
=======
                                uu____5006 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____5009 ->
>>>>>>> origin/guido_tactics
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
<<<<<<< HEAD
                              let uu____4852 =
                                let uu____4853 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4853
                                  None in
                              FStar_Util.Inr uu____4852 in
=======
                              let uu____5019 =
                                let uu____5020 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____5020
                                  None in
                              FStar_Util.Inr uu____5019 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                  let uu____4873 =
                    let uu____4874 =
                      let uu____4882 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4882) in
                    FStar_Syntax_Syntax.Tm_let uu____4874 in
                  FStar_All.pipe_left mk1 uu____4873 in
=======
                  let uu____5040 =
                    let uu____5041 =
                      let uu____5049 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____5049) in
                    FStar_Syntax_Syntax.Tm_let uu____5041 in
                  FStar_All.pipe_left mk1 uu____5040 in
>>>>>>> origin/guido_tactics
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
<<<<<<< HEAD
              let uu____4909 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4909 with
=======
              let uu____5076 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____5076 with
>>>>>>> origin/guido_tactics
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
<<<<<<< HEAD
                          let uu____4930 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4930 None in
=======
                          let uu____5097 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____5097 None in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                    | LocalBinder (x,uu____4938) ->
=======
                    | LocalBinder (x,uu____5105) ->
>>>>>>> origin/guido_tactics
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
<<<<<<< HEAD
                                FStar_Syntax_Syntax.Pat_wild uu____4941;
                              FStar_Syntax_Syntax.p = uu____4942;_}::[] ->
                              body1
                          | uu____4945 ->
                              let uu____4947 =
                                let uu____4950 =
                                  let uu____4951 =
                                    let uu____4966 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4967 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4966, uu____4967) in
                                  FStar_Syntax_Syntax.Tm_match uu____4951 in
                                FStar_Syntax_Syntax.mk uu____4950 in
                              uu____4947 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4980 =
                          let uu____4981 =
                            let uu____4989 =
                              let uu____4990 =
                                let uu____4991 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4991] in
                              FStar_Syntax_Subst.close uu____4990 body2 in
=======
                                FStar_Syntax_Syntax.Pat_wild uu____5108;
                              FStar_Syntax_Syntax.ty = uu____5109;
                              FStar_Syntax_Syntax.p = uu____5110;_}::[] ->
                              body1
                          | uu____5115 ->
                              let uu____5117 =
                                let uu____5120 =
                                  let uu____5121 =
                                    let uu____5137 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____5138 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____5137, uu____5138) in
                                  FStar_Syntax_Syntax.Tm_match uu____5121 in
                                FStar_Syntax_Syntax.mk uu____5120 in
                              uu____5117 None body1.FStar_Syntax_Syntax.pos in
                        let uu____5151 =
                          let uu____5152 =
                            let uu____5160 =
                              let uu____5161 =
                                let uu____5162 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____5162] in
                              FStar_Syntax_Subst.close uu____5161 body2 in
>>>>>>> origin/guido_tactics
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
<<<<<<< HEAD
                              uu____4989) in
                          FStar_Syntax_Syntax.Tm_let uu____4981 in
                        FStar_All.pipe_left mk1 uu____4980 in
=======
                              uu____5160) in
                          FStar_Syntax_Syntax.Tm_let uu____5152 in
                        FStar_All.pipe_left mk1 uu____5151 in
>>>>>>> origin/guido_tactics
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
<<<<<<< HEAD
            let uu____5011 = is_rec || (is_app_pattern pat) in
            if uu____5011
=======
            let uu____5182 = is_rec || (is_app_pattern pat) in
            if uu____5182
>>>>>>> origin/guido_tactics
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
<<<<<<< HEAD
              let uu____5020 =
                let uu____5021 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5021 in
              mk1 uu____5020 in
            let uu____5022 =
              let uu____5023 =
                let uu____5038 =
                  let uu____5041 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5041
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5059 =
                  let uu____5068 =
                    let uu____5076 =
=======
              let uu____5191 =
                let uu____5192 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5192 in
              mk1 uu____5191 in
            let uu____5193 =
              let uu____5194 =
                let uu____5210 =
                  let uu____5213 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5213
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5231 =
                  let uu____5241 =
                    let uu____5250 =
>>>>>>> origin/guido_tactics
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
<<<<<<< HEAD
                    let uu____5078 = desugar_term env t2 in
                    (uu____5076, None, uu____5078) in
                  let uu____5085 =
                    let uu____5094 =
                      let uu____5102 =
=======
                    let uu____5253 = desugar_term env t2 in
                    (uu____5250, None, uu____5253) in
                  let uu____5261 =
                    let uu____5271 =
                      let uu____5280 =
>>>>>>> origin/guido_tactics
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
<<<<<<< HEAD
                      let uu____5104 = desugar_term env t3 in
                      (uu____5102, None, uu____5104) in
                    [uu____5094] in
                  uu____5068 :: uu____5085 in
                (uu____5038, uu____5059) in
              FStar_Syntax_Syntax.Tm_match uu____5023 in
            mk1 uu____5022
=======
                      let uu____5283 = desugar_term env t3 in
                      (uu____5280, None, uu____5283) in
                    [uu____5271] in
                  uu____5241 :: uu____5261 in
                (uu____5210, uu____5231) in
              FStar_Syntax_Syntax.Tm_match uu____5194 in
            mk1 uu____5193
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            let desugar_branch uu____5188 =
              match uu____5188 with
              | (pat,wopt,b) ->
                  let uu____5199 = desugar_match_pat env pat in
                  (match uu____5199 with
=======
            let desugar_branch uu____5372 =
              match uu____5372 with
              | (pat,wopt,b) ->
                  let uu____5383 = desugar_match_pat env pat in
                  (match uu____5383 with
>>>>>>> origin/guido_tactics
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
<<<<<<< HEAD
                             let uu____5212 = desugar_term env1 e1 in
                             Some uu____5212 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5214 =
              let uu____5215 =
                let uu____5230 = desugar_term env e in
                let uu____5231 = FStar_List.collect desugar_branch branches in
                (uu____5230, uu____5231) in
              FStar_Syntax_Syntax.Tm_match uu____5215 in
            FStar_All.pipe_left mk1 uu____5214
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5250 = is_comp_type env t in
              if uu____5250
              then
                let uu____5255 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5255
              else
                (let uu____5261 = desugar_term env t in
                 FStar_Util.Inl uu____5261) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5266 =
              let uu____5267 =
                let uu____5285 = desugar_term env e in
                (uu____5285, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5267 in
            FStar_All.pipe_left mk1 uu____5266
        | FStar_Parser_AST.Record (uu____5301,[]) ->
=======
                             let uu____5396 = desugar_term env1 e1 in
                             Some uu____5396 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5398 =
              let uu____5399 =
                let uu____5415 = desugar_term env e in
                let uu____5416 = FStar_List.collect desugar_branch branches in
                (uu____5415, uu____5416) in
              FStar_Syntax_Syntax.Tm_match uu____5399 in
            FStar_All.pipe_left mk1 uu____5398
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5435 = is_comp_type env t in
              if uu____5435
              then
                let uu____5440 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5440
              else
                (let uu____5446 = desugar_term env t in
                 FStar_Util.Inl uu____5446) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5451 =
              let uu____5452 =
                let uu____5470 = desugar_term env e in
                (uu____5470, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5452 in
            FStar_All.pipe_left mk1 uu____5451
        | FStar_Parser_AST.Record (uu____5486,[]) ->
>>>>>>> origin/guido_tactics
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
<<<<<<< HEAD
              let uu____5322 = FStar_List.hd fields in
              match uu____5322 with | (f,uu____5329) -> f.FStar_Ident.ns in
=======
              let uu____5507 = FStar_List.hd fields in
              match uu____5507 with | (f,uu____5514) -> f.FStar_Ident.ns in
>>>>>>> origin/guido_tactics
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
<<<<<<< HEAD
                     (fun uu____5356  ->
                        match uu____5356 with
                        | (g,uu____5360) ->
=======
                     (fun uu____5538  ->
                        match uu____5538 with
                        | (g,uu____5542) ->
>>>>>>> origin/guido_tactics
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
<<<<<<< HEAD
              | Some (uu____5364,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5372 =
                         let uu____5373 =
                           let uu____5376 =
=======
              | Some (uu____5546,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5554 =
                         let uu____5555 =
                           let uu____5558 =
>>>>>>> origin/guido_tactics
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
<<<<<<< HEAD
                           (uu____5376, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5373 in
                       raise uu____5372
=======
                           (uu____5558, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5555 in
                       raise uu____5554
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                  let uu____5382 =
                    let uu____5388 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5406  ->
                              match uu____5406 with
                              | (f,uu____5412) ->
                                  let uu____5413 =
                                    let uu____5414 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5414 in
                                  (uu____5413, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5388) in
                  FStar_Parser_AST.Construct uu____5382
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5425 =
                      let uu____5426 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5426 in
                    FStar_Parser_AST.mk_term uu____5425 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5428 =
                      let uu____5435 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5452  ->
                                match uu____5452 with
                                | (f,uu____5458) -> get_field (Some xterm) f)) in
                      (None, uu____5435) in
                    FStar_Parser_AST.Record uu____5428 in
=======
                  let uu____5564 =
                    let uu____5570 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5584  ->
                              match uu____5584 with
                              | (f,uu____5590) ->
                                  let uu____5591 =
                                    let uu____5592 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5592 in
                                  (uu____5591, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5570) in
                  FStar_Parser_AST.Construct uu____5564
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5603 =
                      let uu____5604 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5604 in
                    FStar_Parser_AST.mk_term uu____5603 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5606 =
                      let uu____5613 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5627  ->
                                match uu____5627 with
                                | (f,uu____5633) -> get_field (Some xterm) f)) in
                      (None, uu____5613) in
                    FStar_Parser_AST.Record uu____5606 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                         FStar_Syntax_Syntax.tk = uu____5474;
                         FStar_Syntax_Syntax.pos = uu____5475;
                         FStar_Syntax_Syntax.vars = uu____5476;_},args);
                    FStar_Syntax_Syntax.tk = uu____5478;
                    FStar_Syntax_Syntax.pos = uu____5479;
                    FStar_Syntax_Syntax.vars = uu____5480;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5502 =
                     let uu____5503 =
                       let uu____5513 =
                         let uu____5514 =
                           let uu____5516 =
                             let uu____5517 =
                               let uu____5521 =
=======
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
>>>>>>> origin/guido_tactics
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
<<<<<<< HEAD
                                 uu____5521) in
                             FStar_Syntax_Syntax.Record_ctor uu____5517 in
                           Some uu____5516 in
=======
                                 uu____5696) in
                             FStar_Syntax_Syntax.Record_ctor uu____5692 in
                           Some uu____5691 in
>>>>>>> origin/guido_tactics
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
<<<<<<< HEAD
                           FStar_Syntax_Syntax.Delta_constant uu____5514 in
                       (uu____5513, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5503 in
                   FStar_All.pipe_left mk1 uu____5502 in
=======
                           FStar_Syntax_Syntax.Delta_constant uu____5689 in
                       (uu____5688, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5678 in
                   FStar_All.pipe_left mk1 uu____5677 in
>>>>>>> origin/guido_tactics
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
<<<<<<< HEAD
             | uu____5541 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5545 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5545 with
=======
             | uu____5720 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5724 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5724 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                  let uu____5558 =
                    let uu____5559 =
                      let uu____5569 =
=======
                  let uu____5737 =
                    let uu____5738 =
                      let uu____5748 =
>>>>>>> origin/guido_tactics
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
<<<<<<< HEAD
                      let uu____5570 =
                        let uu____5572 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5572] in
                      (uu____5569, uu____5570) in
                    FStar_Syntax_Syntax.Tm_app uu____5559 in
                  FStar_All.pipe_left mk1 uu____5558))
        | FStar_Parser_AST.NamedTyp (uu____5576,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5579 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5580 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5581,uu____5582,uu____5583) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5590,uu____5591,uu____5592) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5599,uu____5600,uu____5601) ->
=======
                      let uu____5749 =
                        let uu____5751 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5751] in
                      (uu____5748, uu____5749) in
                    FStar_Syntax_Syntax.Tm_app uu____5738 in
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
>>>>>>> origin/guido_tactics
            failwith "Not implemented yet"
and desugar_args:
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term* FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option)
        Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
<<<<<<< HEAD
           (fun uu____5629  ->
              match uu____5629 with
              | (a,imp) ->
                  let uu____5637 = desugar_term env a in
                  arg_withimp_e imp uu____5637))
=======
           (fun uu____5804  ->
              match uu____5804 with
              | (a,imp) ->
                  let uu____5812 = desugar_term env a in
                  arg_withimp_e imp uu____5812))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let is_requires uu____5654 =
          match uu____5654 with
          | (t1,uu____5658) ->
              let uu____5659 =
                let uu____5660 = unparen t1 in uu____5660.FStar_Parser_AST.tm in
              (match uu____5659 with
               | FStar_Parser_AST.Requires uu____5661 -> true
               | uu____5665 -> false) in
        let is_ensures uu____5671 =
          match uu____5671 with
          | (t1,uu____5675) ->
              let uu____5676 =
                let uu____5677 = unparen t1 in uu____5677.FStar_Parser_AST.tm in
              (match uu____5676 with
               | FStar_Parser_AST.Ensures uu____5678 -> true
               | uu____5682 -> false) in
        let is_app head1 uu____5691 =
          match uu____5691 with
          | (t1,uu____5695) ->
              let uu____5696 =
                let uu____5697 = unparen t1 in uu____5697.FStar_Parser_AST.tm in
              (match uu____5696 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5699;
                      FStar_Parser_AST.level = uu____5700;_},uu____5701,uu____5702)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5703 -> false) in
        let is_smt_pat uu____5709 =
          match uu____5709 with
          | (t1,uu____5713) ->
              let uu____5714 =
                let uu____5715 = unparen t1 in uu____5715.FStar_Parser_AST.tm in
              (match uu____5714 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5718);
                             FStar_Parser_AST.range = uu____5719;
                             FStar_Parser_AST.level = uu____5720;_},uu____5721)::uu____5722::[])
=======
        let is_requires uu____5829 =
          match uu____5829 with
          | (t1,uu____5833) ->
              let uu____5834 =
                let uu____5835 = unparen t1 in uu____5835.FStar_Parser_AST.tm in
              (match uu____5834 with
               | FStar_Parser_AST.Requires uu____5836 -> true
               | uu____5840 -> false) in
        let is_ensures uu____5846 =
          match uu____5846 with
          | (t1,uu____5850) ->
              let uu____5851 =
                let uu____5852 = unparen t1 in uu____5852.FStar_Parser_AST.tm in
              (match uu____5851 with
               | FStar_Parser_AST.Ensures uu____5853 -> true
               | uu____5857 -> false) in
        let is_app head1 uu____5866 =
          match uu____5866 with
          | (t1,uu____5870) ->
              let uu____5871 =
                let uu____5872 = unparen t1 in uu____5872.FStar_Parser_AST.tm in
              (match uu____5871 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5874;
                      FStar_Parser_AST.level = uu____5875;_},uu____5876,uu____5877)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5878 -> false) in
        let is_smt_pat uu____5884 =
          match uu____5884 with
          | (t1,uu____5888) ->
              let uu____5889 =
                let uu____5890 = unparen t1 in uu____5890.FStar_Parser_AST.tm in
              (match uu____5889 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5893);
                             FStar_Parser_AST.range = uu____5894;
                             FStar_Parser_AST.level = uu____5895;_},uu____5896)::uu____5897::[])
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                             FStar_Parser_AST.range = uu____5744;
                             FStar_Parser_AST.level = uu____5745;_},uu____5746)::uu____5747::[])
=======
                             FStar_Parser_AST.range = uu____5918;
                             FStar_Parser_AST.level = uu____5919;_},uu____5920)::uu____5921::[])
>>>>>>> origin/guido_tactics
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
<<<<<<< HEAD
               | uu____5761 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5779 = head_and_args t1 in
          match uu____5779 with
=======
               | uu____5934 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5952 = head_and_args t1 in
          match uu____5952 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                   let uu____5996 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5996, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6012 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6012
=======
                   let uu____6169 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____6169, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6183 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6183
>>>>>>> origin/guido_tactics
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
<<<<<<< HEAD
                   (let uu____6023 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6023
=======
                   (let uu____6192 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6192
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
               | uu____6043 ->
                   let default_effect =
                     let uu____6045 = FStar_Options.ml_ish () in
                     if uu____6045
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6048 =
                           FStar_Options.warn_default_effects () in
                         if uu____6048
=======
               | uu____6212 ->
                   let default_effect =
                     let uu____6214 = FStar_Options.ml_ish () in
                     if uu____6214
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6217 =
                           FStar_Options.warn_default_effects () in
                         if uu____6217
>>>>>>> origin/guido_tactics
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
<<<<<<< HEAD
        let uu____6061 = pre_process_comp_typ t in
        match uu____6061 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6091 =
                  let uu____6092 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6092 in
                fail uu____6091)
             else ();
             (let is_universe uu____6099 =
                match uu____6099 with
                | (uu____6102,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6104 = FStar_Util.take is_universe args in
              match uu____6104 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6138  ->
                         match uu____6138 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6143 =
                    let uu____6151 = FStar_List.hd args1 in
                    let uu____6156 = FStar_List.tl args1 in
                    (uu____6151, uu____6156) in
                  (match uu____6143 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6187 =
                         let is_decrease uu____6210 =
                           match uu____6210 with
                           | (t1,uu____6217) ->
=======
        let uu____6230 = pre_process_comp_typ t in
        match uu____6230 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6262 =
                  let uu____6263 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6263 in
                fail uu____6262)
             else ();
             (let is_universe uu____6270 =
                match uu____6270 with
                | (uu____6273,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6275 = FStar_Util.take is_universe args in
              match uu____6275 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6306  ->
                         match uu____6306 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6311 =
                    let uu____6319 = FStar_List.hd args1 in
                    let uu____6324 = FStar_List.tl args1 in
                    (uu____6319, uu____6324) in
                  (match uu____6311 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6355 =
                         let is_decrease uu____6378 =
                           match uu____6378 with
                           | (t1,uu____6385) ->
>>>>>>> origin/guido_tactics
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
                                       FStar_Syntax_Syntax.tk = uu____6225;
                                       FStar_Syntax_Syntax.pos = uu____6226;
                                       FStar_Syntax_Syntax.vars = uu____6227;_},uu____6228::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6250 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6187 with
=======
                                       FStar_Syntax_Syntax.tk = uu____6393;
                                       FStar_Syntax_Syntax.pos = uu____6394;
                                       FStar_Syntax_Syntax.vars = uu____6395;_},uu____6396::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6418 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6355 with
>>>>>>> origin/guido_tactics
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
<<<<<<< HEAD
                                   (fun uu____6322  ->
                                      match uu____6322 with
                                      | (t1,uu____6329) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6336,(arg,uu____6338)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6360 -> failwith "impos"))) in
=======
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
                                           | uu____6522 -> failwith "impos"))) in
>>>>>>> origin/guido_tactics
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
<<<<<<< HEAD
                                | uu____6372 -> false in
=======
                                | uu____6534 -> false in
>>>>>>> origin/guido_tactics
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
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   None in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
<<<<<<< HEAD
                                           | uu____6473 -> pat in
                                         let uu____6474 =
                                           let uu____6481 =
                                             let uu____6488 =
                                               let uu____6494 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6494, aq) in
                                             [uu____6488] in
                                           ens :: uu____6481 in
                                         req :: uu____6474
                                     | uu____6526 -> rest2
=======
                                           | uu____6637 -> pat in
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
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6658, aq) in
                                             [uu____6652] in
                                           ens :: uu____6645 in
                                         req :: uu____6638
                                     | uu____6694 -> rest2
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        | uu____6542 -> None in
      let mk1 t = FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___234_6563 = t in
        {
          FStar_Syntax_Syntax.n = (uu___234_6563.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___234_6563.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___234_6563.FStar_Syntax_Syntax.vars)
=======
        | uu____6710 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___236_6735 = t in
        {
          FStar_Syntax_Syntax.n = (uu___236_6735.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___236_6735.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___236_6735.FStar_Syntax_Syntax.vars)
>>>>>>> origin/guido_tactics
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
<<<<<<< HEAD
            (let uu___235_6594 = b in
             {
               FStar_Parser_AST.b = (uu___235_6594.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___235_6594.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___235_6594.FStar_Parser_AST.aqual)
=======
            (let uu___237_6765 = b in
             {
               FStar_Parser_AST.b = (uu___237_6765.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___237_6765.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___237_6765.FStar_Parser_AST.aqual)
>>>>>>> origin/guido_tactics
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
<<<<<<< HEAD
                       let uu____6630 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6630)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6639 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6639 with
             | (env1,a1) ->
                 let a2 =
                   let uu___236_6647 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___236_6647.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___236_6647.FStar_Syntax_Syntax.index);
=======
                       let uu____6798 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6798)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6807 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6807 with
             | (env1,a1) ->
                 let a2 =
                   let uu___238_6815 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___238_6815.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___238_6815.FStar_Syntax_Syntax.index);
>>>>>>> origin/guido_tactics
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
<<<<<<< HEAD
                   | uu____6660 ->
=======
                   | uu____6828 ->
>>>>>>> origin/guido_tactics
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
<<<<<<< HEAD
                   let uu____6669 =
                     let uu____6672 =
                       let uu____6673 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6673] in
                     no_annot_abs uu____6672 body2 in
                   FStar_All.pipe_left setpos uu____6669 in
                 let uu____6678 =
                   let uu____6679 =
                     let uu____6689 =
=======
                   let uu____6837 =
                     let uu____6840 =
                       let uu____6841 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6841] in
                     no_annot_abs uu____6840 body2 in
                   FStar_All.pipe_left setpos uu____6837 in
                 let uu____6846 =
                   let uu____6847 =
                     let uu____6857 =
>>>>>>> origin/guido_tactics
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
<<<<<<< HEAD
                     let uu____6690 =
                       let uu____6692 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6692] in
                     (uu____6689, uu____6690) in
                   FStar_Syntax_Syntax.Tm_app uu____6679 in
                 FStar_All.pipe_left mk1 uu____6678)
        | uu____6696 -> failwith "impossible" in
=======
                     let uu____6858 =
                       let uu____6860 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6860] in
                     (uu____6857, uu____6858) in
                   FStar_Syntax_Syntax.Tm_app uu____6847 in
                 FStar_All.pipe_left mk1 uu____6846)
        | uu____6864 -> failwith "impossible" in
>>>>>>> origin/guido_tactics
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
<<<<<<< HEAD
              let uu____6745 = q (rest, pats, body) in
              let uu____6749 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6745 uu____6749
                FStar_Parser_AST.Formula in
            let uu____6750 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6750 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6755 -> failwith "impossible" in
      let uu____6757 =
        let uu____6758 = unparen f in uu____6758.FStar_Parser_AST.tm in
      match uu____6757 with
=======
              let uu____6913 = q (rest, pats, body) in
              let uu____6917 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6913 uu____6917
                FStar_Parser_AST.Formula in
            let uu____6918 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6918 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6923 -> failwith "impossible" in
      let uu____6925 =
        let uu____6926 = unparen f in uu____6926.FStar_Parser_AST.tm in
      match uu____6925 with
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
<<<<<<< HEAD
      | FStar_Parser_AST.QForall ([],uu____6765,uu____6766) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6772,uu____6773) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6792 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6792
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6815 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6815
=======
      | FStar_Parser_AST.QForall ([],uu____6933,uu____6934) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6940,uu____6941) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6960 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6960
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6981 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6981
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
<<<<<<< HEAD
      | uu____6842 -> desugar_term env f
=======
      | uu____7006 -> desugar_term env f
>>>>>>> origin/guido_tactics
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
<<<<<<< HEAD
      let uu____6846 =
        FStar_List.fold_left
          (fun uu____6870  ->
             fun b  ->
               match uu____6870 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___237_6899 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___237_6899.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___237_6899.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___237_6899.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6909 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6909 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___238_6921 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___238_6921.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___238_6921.FStar_Syntax_Syntax.index);
=======
      let uu____7010 =
        FStar_List.fold_left
          (fun uu____7023  ->
             fun b  ->
               match uu____7023 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___239_7051 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___239_7051.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___239_7051.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___239_7051.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____7061 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____7061 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___240_7073 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___240_7073.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___240_7073.FStar_Syntax_Syntax.index);
>>>>>>> origin/guido_tactics
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
<<<<<<< HEAD
                    | uu____6930 ->
=======
                    | uu____7082 ->
>>>>>>> origin/guido_tactics
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
<<<<<<< HEAD
      match uu____6846 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
=======
      match uu____7010 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
>>>>>>> origin/guido_tactics
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
<<<<<<< HEAD
          let uu____6977 = desugar_typ env t in ((Some x), uu____6977)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6981 = desugar_typ env t in ((Some x), uu____6981)
      | FStar_Parser_AST.TVariable x ->
          let uu____6984 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              None x.FStar_Ident.idRange in
          ((Some x), uu____6984)
      | FStar_Parser_AST.NoName t ->
          let uu____6995 = desugar_typ env t in (None, uu____6995)
=======
          let uu____7132 = desugar_typ env t in ((Some x), uu____7132)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7136 = desugar_typ env t in ((Some x), uu____7136)
      | FStar_Parser_AST.TVariable x ->
          let uu____7139 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____7139)
      | FStar_Parser_AST.NoName t ->
          let uu____7154 = desugar_typ env t in (None, uu____7154)
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
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
<<<<<<< HEAD
               (fun uu___208_7018  ->
                  match uu___208_7018 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7019 -> false)) in
        let quals2 q =
          let uu____7027 =
            (let uu____7030 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7030) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7027
=======
               (fun uu___210_7179  ->
                  match uu___210_7179 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7180 -> false)) in
        let quals2 q =
          let uu____7188 =
            (let uu____7189 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7189) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7188
>>>>>>> origin/guido_tactics
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
<<<<<<< HEAD
                let uu____7040 =
=======
                let uu____7196 =
>>>>>>> origin/guido_tactics
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
<<<<<<< HEAD
                  FStar_Syntax_Syntax.sigquals = uu____7040;
=======
                  FStar_Syntax_Syntax.sigquals = uu____7196;
>>>>>>> origin/guido_tactics
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
            let uu____7064 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7086  ->
                        match uu____7086 with
                        | (x,uu____7091) ->
                            let uu____7092 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7092 with
                             | (field_name,uu____7097) ->
                                 let only_decl =
                                   ((let uu____7101 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7101)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7103 =
                                        let uu____7104 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7104.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7103) in
=======
            let uu____7225 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7235  ->
                        match uu____7235 with
                        | (x,uu____7240) ->
                            let uu____7241 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7241 with
                             | (field_name,uu____7246) ->
                                 let only_decl =
                                   ((let uu____7248 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7248)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7249 =
                                        let uu____7250 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7250.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7249) in
>>>>>>> origin/guido_tactics
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
<<<<<<< HEAD
                                     let uu____7114 =
                                       FStar_List.filter
                                         (fun uu___209_7117  ->
                                            match uu___209_7117 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7118 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7114
=======
                                     let uu____7260 =
                                       FStar_List.filter
                                         (fun uu___211_7262  ->
                                            match uu___211_7262 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7263 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7260
>>>>>>> origin/guido_tactics
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
<<<<<<< HEAD
                                          (fun uu___210_7127  ->
                                             match uu___210_7127 with
=======
                                          (fun uu___212_7271  ->
                                             match uu___212_7271 with
>>>>>>> origin/guido_tactics
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
<<<<<<< HEAD
                                             | uu____7128 -> false)) in
=======
                                             | uu____7272 -> false)) in
>>>>>>> origin/guido_tactics
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
                                       FStar_Syntax_Syntax.default_sigmeta
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
<<<<<<< HEAD
                                      let uu____7134 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7134
=======
                                      let uu____7278 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7278
>>>>>>> origin/guido_tactics
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
<<<<<<< HEAD
                                      let uu____7138 =
                                        let uu____7141 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7141 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7138;
=======
                                      let uu____7282 =
                                        let uu____7285 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7285 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7282;
>>>>>>> origin/guido_tactics
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
<<<<<<< HEAD
                                      let uu____7143 =
                                        let uu____7144 =
                                          let uu____7150 =
                                            let uu____7152 =
                                              let uu____7153 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7153
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7152] in
                                          ((false, [lb]), uu____7150, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7144 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7143;
=======
                                      let uu____7287 =
                                        let uu____7288 =
                                          let uu____7294 =
                                            let uu____7296 =
                                              let uu____7297 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7297
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7296] in
                                          ((false, [lb]), uu____7294, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7288 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7287;
>>>>>>> origin/guido_tactics
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
<<<<<<< HEAD
            FStar_All.pipe_right uu____7064 FStar_List.flatten
=======
            FStar_All.pipe_right uu____7225 FStar_List.flatten
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            (lid,uu____7183,t,uu____7185,n1,uu____7187) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7190 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7190 with
             | (formals,uu____7200) ->
                 (match formals with
                  | [] -> []
                  | uu____7214 ->
                      let filter_records uu___211_7222 =
                        match uu___211_7222 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7224,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7231 -> None in
                      let fv_qual =
                        let uu____7233 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7233 with
=======
            (lid,uu____7333,t,uu____7335,n1,uu____7337) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7340 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7340 with
             | (formals,uu____7350) ->
                 (match formals with
                  | [] -> []
                  | uu____7364 ->
                      let filter_records uu___213_7372 =
                        match uu___213_7372 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7374,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7381 -> None in
                      let fv_qual =
                        let uu____7383 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7383 with
>>>>>>> origin/guido_tactics
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
<<<<<<< HEAD
                      let uu____7240 = FStar_Util.first_N n1 formals in
                      (match uu____7240 with
                       | (uu____7252,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7266 -> []
=======
                      let uu____7390 = FStar_Util.first_N n1 formals in
                      (match uu____7390 with
                       | (uu____7402,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7416 -> []
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                    let uu____7304 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7304
                    then
                      let uu____7306 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7306
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7309 =
                      let uu____7312 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7312 in
                    let uu____7313 =
                      let uu____7316 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7316 in
                    let uu____7319 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7309;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7313;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7319
=======
                    let uu____7462 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7462
                    then
                      let uu____7464 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7464
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7467 =
                      let uu____7470 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7470 in
                    let uu____7471 =
                      let uu____7474 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7474 in
                    let uu____7477 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7467;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7471;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7477
>>>>>>> origin/guido_tactics
                    } in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids, []));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
          let tycon_id uu___212_7352 =
            match uu___212_7352 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7354,uu____7355) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7361,uu____7362,uu____7363) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7369,uu____7370,uu____7371) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7387,uu____7388,uu____7389) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7413) ->
                let uu____7414 =
                  let uu____7415 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7415 in
                FStar_Parser_AST.mk_term uu____7414 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7417 =
                  let uu____7418 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7418 in
                FStar_Parser_AST.mk_term uu____7417 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7420) ->
=======
          let tycon_id uu___214_7514 =
            match uu___214_7514 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7516,uu____7517) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7523,uu____7524,uu____7525) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7531,uu____7532,uu____7533) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7549,uu____7550,uu____7551) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7575) ->
                let uu____7576 =
                  let uu____7577 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7577 in
                FStar_Parser_AST.mk_term uu____7576 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7579 =
                  let uu____7580 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7580 in
                FStar_Parser_AST.mk_term uu____7579 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7582) ->
>>>>>>> origin/guido_tactics
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
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
<<<<<<< HEAD
              | uu____7441 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7447 =
                     let uu____7448 =
                       let uu____7452 = binder_to_term b in
                       (out, uu____7452, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7448 in
                   FStar_Parser_AST.mk_term uu____7447
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___213_7459 =
            match uu___213_7459 with
=======
              | uu____7603 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7606 =
                     let uu____7607 =
                       let uu____7611 = binder_to_term b in
                       (out, uu____7611, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7607 in
                   FStar_Parser_AST.mk_term uu____7606
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___215_7618 =
            match uu___215_7618 with
>>>>>>> origin/guido_tactics
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
<<<<<<< HEAD
                    (fun uu____7492  ->
                       match uu____7492 with
                       | (x,t,uu____7499) ->
=======
                    (fun uu____7647  ->
                       match uu____7647 with
                       | (x,t,uu____7654) ->
>>>>>>> origin/guido_tactics
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
<<<<<<< HEAD
                  let uu____7503 =
                    let uu____7504 =
                      let uu____7505 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7505 in
                    FStar_Parser_AST.mk_term uu____7504
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7503 parms in
=======
                  let uu____7658 =
                    let uu____7659 =
                      let uu____7660 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7660 in
                    FStar_Parser_AST.mk_term uu____7659
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7658 parms in
>>>>>>> origin/guido_tactics
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
<<<<<<< HEAD
                let uu____7508 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7524  ->
                          match uu____7524 with
                          | (x,uu____7530,uu____7531) ->
=======
                let uu____7663 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7675  ->
                          match uu____7675 with
                          | (x,uu____7681,uu____7682) ->
>>>>>>> origin/guido_tactics
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
<<<<<<< HEAD
                  uu____7508)
            | uu____7558 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___214_7580 =
            match uu___214_7580 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7594 = typars_of_binders _env binders in
                (match uu____7594 with
=======
                  uu____7663)
            | uu____7709 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___216_7731 =
            match uu___216_7731 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7745 = typars_of_binders _env binders in
                (match uu____7745 with
>>>>>>> origin/guido_tactics
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
<<<<<<< HEAD
                       let uu____7622 =
                         let uu____7623 =
                           let uu____7624 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7624 in
                         FStar_Parser_AST.mk_term uu____7623
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7622 binders in
=======
                       let uu____7773 =
                         let uu____7774 =
                           let uu____7775 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7775 in
                         FStar_Parser_AST.mk_term uu____7774
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7773 binders in
>>>>>>> origin/guido_tactics
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
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
<<<<<<< HEAD
            | uu____7634 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7660 =
              FStar_List.fold_left
                (fun uu____7685  ->
                   fun uu____7686  ->
                     match (uu____7685, uu____7686) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7734 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7734 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7660 with
=======
            | uu____7785 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7811 =
              FStar_List.fold_left
                (fun uu____7827  ->
                   fun uu____7828  ->
                     match (uu____7827, uu____7828) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7876 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7876 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7811 with
>>>>>>> origin/guido_tactics
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
<<<<<<< HEAD
                    let uu____7795 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7795
                | uu____7796 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7801 = desugar_abstract_tc quals env [] tc in
              (match uu____7801 with
               | (uu____7808,uu____7809,se,uu____7811) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7814,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7823 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7823
                           then quals1
                           else
                             ((let uu____7828 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7829 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7828 uu____7829);
=======
                    let uu____7937 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7937
                | uu____7938 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7943 = desugar_abstract_tc quals env [] tc in
              (match uu____7943 with
               | (uu____7950,uu____7951,se,uu____7953) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7956,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7965 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7965
                           then quals1
                           else
                             ((let uu____7970 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7971 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7970 uu____7971);
>>>>>>> origin/guido_tactics
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
<<<<<<< HEAD
                           | uu____7833 ->
                               let uu____7834 =
                                 let uu____7837 =
                                   let uu____7838 =
                                     let uu____7846 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7846) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7838 in
                                 FStar_Syntax_Syntax.mk uu____7837 in
                               uu____7834 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___239_7855 = se in
=======
                           | uu____7975 ->
                               let uu____7976 =
                                 let uu____7979 =
                                   let uu____7980 =
                                     let uu____7988 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7988) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7980 in
                                 FStar_Syntax_Syntax.mk uu____7979 in
                               uu____7976 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___241_7997 = se in
>>>>>>> origin/guido_tactics
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                             (uu___239_7855.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___239_7855.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7857 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7860 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7860
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7870 = typars_of_binders env binders in
              (match uu____7870 with
=======
                             (uu___241_7997.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_7997.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7999 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____8002 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____8002
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____8012 = typars_of_binders env binders in
              (match uu____8012 with
>>>>>>> origin/guido_tactics
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
<<<<<<< HEAD
                         let uu____7890 =
                           FStar_Util.for_some
                             (fun uu___215_7892  ->
                                match uu___215_7892 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7893 -> false) quals in
                         if uu____7890
=======
                         let uu____8032 =
                           FStar_Util.for_some
                             (fun uu___217_8033  ->
                                match uu___217_8033 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____8034 -> false) quals in
                         if uu____8032
>>>>>>> origin/guido_tactics
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
<<<<<<< HEAD
                     let uu____7899 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___216_7902  ->
                               match uu___216_7902 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7903 -> false)) in
                     if uu____7899
=======
                     let uu____8040 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___218_8042  ->
                               match uu___218_8042 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____8043 -> false)) in
                     if uu____8040
>>>>>>> origin/guido_tactics
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
<<<<<<< HEAD
                     let uu____7910 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7910
                     then
                       let uu____7912 =
                         let uu____7916 =
                           let uu____7917 = unparen t in
                           uu____7917.FStar_Parser_AST.tm in
                         match uu____7916 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7929 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7945)::args_rev ->
                                   let uu____7952 =
                                     let uu____7953 = unparen last_arg in
                                     uu____7953.FStar_Parser_AST.tm in
                                   (match uu____7952 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7968 -> ([], args))
                               | uu____7973 -> ([], args) in
                             (match uu____7929 with
                              | (cattributes,args1) ->
                                  let uu____7994 =
=======
                     let uu____8050 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____8050
                     then
                       let uu____8052 =
                         let uu____8056 =
                           let uu____8057 = unparen t in
                           uu____8057.FStar_Parser_AST.tm in
                         match uu____8056 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____8069 =
                               match FStar_List.rev args with
                               | (last_arg,uu____8085)::args_rev ->
                                   let uu____8092 =
                                     let uu____8093 = unparen last_arg in
                                     uu____8093.FStar_Parser_AST.tm in
                                   (match uu____8092 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____8108 -> ([], args))
                               | uu____8113 -> ([], args) in
                             (match uu____8069 with
                              | (cattributes,args1) ->
                                  let uu____8134 =
>>>>>>> origin/guido_tactics
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
<<<<<<< HEAD
                                      t.FStar_Parser_AST.level), uu____7994))
                         | uu____8000 -> (t, []) in
                       match uu____7912 with
=======
                                      t.FStar_Parser_AST.level), uu____8134))
                         | uu____8140 -> (t, []) in
                       match uu____8052 with
>>>>>>> origin/guido_tactics
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
<<<<<<< HEAD
                                  (fun uu___217_8016  ->
                                     match uu___217_8016 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8017 -> true)) in
=======
                                  (fun uu___219_8155  ->
                                     match uu___219_8155 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8156 -> true)) in
>>>>>>> origin/guido_tactics
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
<<<<<<< HEAD
          | (FStar_Parser_AST.TyconRecord uu____8025)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8038 = tycon_record_as_variant trec in
              (match uu____8038 with
               | (t,fs) ->
                   let uu____8048 =
                     let uu____8050 =
                       let uu____8051 =
                         let uu____8056 =
                           let uu____8058 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8058 in
                         (uu____8056, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8051 in
                     uu____8050 :: quals in
                   desugar_tycon env d uu____8048 [t])
          | uu____8061::uu____8062 ->
=======
          | (FStar_Parser_AST.TyconRecord uu____8164)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8177 = tycon_record_as_variant trec in
              (match uu____8177 with
               | (t,fs) ->
                   let uu____8187 =
                     let uu____8189 =
                       let uu____8190 =
                         let uu____8195 =
                           let uu____8197 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8197 in
                         (uu____8195, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8190 in
                     uu____8189 :: quals in
                   desugar_tycon env d uu____8187 [t])
          | uu____8200::uu____8201 ->
>>>>>>> origin/guido_tactics
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
<<<<<<< HEAD
                let uu____8150 = et in
                match uu____8150 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8264 ->
                         let trec = tc in
                         let uu____8277 = tycon_record_as_variant trec in
                         (match uu____8277 with
                          | (t,fs) ->
                              let uu____8308 =
                                let uu____8310 =
                                  let uu____8311 =
                                    let uu____8316 =
                                      let uu____8318 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8318 in
                                    (uu____8316, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8311 in
                                uu____8310 :: quals1 in
                              collect_tcs uu____8308 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8364 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8364 with
                          | (env2,uu____8395,se,tconstr) ->
=======
                let uu____8288 = et in
                match uu____8288 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8402 ->
                         let trec = tc in
                         let uu____8415 = tycon_record_as_variant trec in
                         (match uu____8415 with
                          | (t,fs) ->
                              let uu____8446 =
                                let uu____8448 =
                                  let uu____8449 =
                                    let uu____8454 =
                                      let uu____8456 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8456 in
                                    (uu____8454, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8449 in
                                uu____8448 :: quals1 in
                              collect_tcs uu____8446 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8502 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8502 with
                          | (env2,uu____8533,se,tconstr) ->
>>>>>>> origin/guido_tactics
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
<<<<<<< HEAD
                         let uu____8473 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8473 with
                          | (env2,uu____8504,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8568 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8592 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8592 with
=======
                         let uu____8611 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8611 with
                          | (env2,uu____8642,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8706 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8730 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8730 with
>>>>>>> origin/guido_tactics
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
<<<<<<< HEAD
                          (fun uu___219_8857  ->
                             match uu___219_8857 with
=======
                          (fun uu___221_8980  ->
                             match uu___221_8980 with
>>>>>>> origin/guido_tactics
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
<<<<<<< HEAD
                                      (id,uvs,tpars,k,uu____8893,uu____8894);
                                    FStar_Syntax_Syntax.sigrng = uu____8895;
                                    FStar_Syntax_Syntax.sigquals = uu____8896;
                                    FStar_Syntax_Syntax.sigmeta = uu____8897;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8929 =
                                     typars_of_binders env1 binders in
                                   match uu____8929 with
                                   | (env2,tpars1) ->
                                       let uu____8946 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8946 with
=======
                                      (id,uvs,tpars,k,uu____9016,uu____9017);
                                    FStar_Syntax_Syntax.sigrng = uu____9018;
                                    FStar_Syntax_Syntax.sigquals = uu____9019;
                                    FStar_Syntax_Syntax.sigmeta = uu____9020;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____9052 =
                                     typars_of_binders env1 binders in
                                   match uu____9052 with
                                   | (env2,tpars1) ->
                                       let uu____9069 =
                                         push_tparams env2 tpars1 in
                                       (match uu____9069 with
>>>>>>> origin/guido_tactics
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
<<<<<<< HEAD
                                 let uu____8965 =
                                   let uu____8976 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8976) in
                                 [uu____8965]
=======
                                 let uu____9088 =
                                   let uu____9099 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____9099) in
                                 [uu____9088]
>>>>>>> origin/guido_tactics
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
<<<<<<< HEAD
                                      (tname,univs,tpars,k,mutuals1,uu____9013);
                                    FStar_Syntax_Syntax.sigrng = uu____9014;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9016;_},constrs,tconstr,quals1)
=======
                                      (tname,univs1,tpars,k,mutuals1,uu____9136);
                                    FStar_Syntax_Syntax.sigrng = uu____9137;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9139;_},constrs,tconstr,quals1)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                 let uu____9068 = push_tparams env1 tpars in
                                 (match uu____9068 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9110  ->
                                             match uu____9110 with
                                             | (x,uu____9118) ->
=======
                                 let uu____9191 = push_tparams env1 tpars in
                                 (match uu____9191 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9230  ->
                                             match uu____9230 with
                                             | (x,uu____9238) ->
>>>>>>> origin/guido_tactics
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
<<<<<<< HEAD
                                      let uu____9123 =
                                        let uu____9138 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9201  ->
                                                  match uu____9201 with
=======
                                      let uu____9243 =
                                        let uu____9258 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9310  ->
                                                  match uu____9310 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                        let uu____9234 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9234 in
=======
                                                        let uu____9343 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9343 in
>>>>>>> origin/guido_tactics
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
<<<<<<< HEAD
                                                                uu___218_9242
                                                                 ->
                                                                match uu___218_9242
=======
                                                                uu___220_9349
                                                                 ->
                                                                match uu___220_9349
>>>>>>> origin/guido_tactics
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
<<<<<<< HEAD
                                                                | uu____9249
=======
                                                                | uu____9356
>>>>>>> origin/guido_tactics
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
<<<<<<< HEAD
                                                      let uu____9255 =
                                                        let uu____9266 =
                                                          let uu____9267 =
                                                            let uu____9268 =
                                                              let uu____9276
                                                                =
                                                                let uu____9279
                                                                  =
                                                                  let uu____9282
=======
                                                      let uu____9363 =
                                                        let uu____9374 =
                                                          let uu____9375 =
                                                            let uu____9376 =
                                                              let uu____9384
                                                                =
                                                                let uu____9387
                                                                  =
                                                                  let uu____9390
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
<<<<<<< HEAD
                                                                    uu____9282 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9279 in
                                                              (name, univs,
                                                                uu____9276,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9268 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9267;
=======
                                                                    uu____9390 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9387 in
                                                              (name, univs1,
                                                                uu____9384,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9376 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9375;
>>>>>>> origin/guido_tactics
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
<<<<<<< HEAD
                                                          uu____9266) in
                                                      (name, uu____9255))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9138 in
                                      (match uu____9123 with
=======
                                                          uu____9374) in
                                                      (name, uu____9363))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9258 in
                                      (match uu____9243 with
>>>>>>> origin/guido_tactics
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
                                                 FStar_Syntax_Syntax.default_sigmeta
                                             })
                                           :: constrs1))
<<<<<<< HEAD
                             | uu____9405 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9474  ->
                             match uu____9474 with
                             | (name_doc,uu____9489,uu____9490) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9533  ->
                             match uu____9533 with
                             | (uu____9544,uu____9545,se) -> se)) in
                   let uu____9561 =
                     let uu____9565 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9565 rng in
                   (match uu____9561 with
=======
                             | uu____9515 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9580  ->
                             match uu____9580 with
                             | (name_doc,uu____9595,uu____9596) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9635  ->
                             match uu____9635 with
                             | (uu____9646,uu____9647,se) -> se)) in
                   let uu____9663 =
                     let uu____9667 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9667 rng in
                   (match uu____9663 with
>>>>>>> origin/guido_tactics
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
<<<<<<< HEAD
                               (fun uu____9603  ->
                                  match uu____9603 with
                                  | (uu____9615,tps,se) ->
=======
                               (fun uu____9701  ->
                                  match uu____9701 with
                                  | (uu____9713,tps,se) ->
>>>>>>> origin/guido_tactics
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
<<<<<<< HEAD
                                      (tname,uu____9648,tps,k,uu____9651,constrs)
=======
                                      (tname,uu____9737,tps,k,uu____9740,constrs)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                  | uu____9666 -> [])) in
=======
                                  | uu____9758 -> [])) in
>>>>>>> origin/guido_tactics
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
<<<<<<< HEAD
                               fun uu____9679  ->
                                 match uu____9679 with
=======
                               fun uu____9767  ->
                                 match uu____9767 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____9701 =
        FStar_List.fold_left
          (fun uu____9718  ->
             fun b  ->
               match uu____9718 with
               | (env1,binders1) ->
                   let uu____9730 = desugar_binder env1 b in
                   (match uu____9730 with
                    | (Some a,k) ->
                        let uu____9740 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9740 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9750 ->
=======
      let uu____9791 =
        FStar_List.fold_left
          (fun uu____9798  ->
             fun b  ->
               match uu____9798 with
               | (env1,binders1) ->
                   let uu____9810 = desugar_binder env1 b in
                   (match uu____9810 with
                    | (Some a,k) ->
                        let uu____9820 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9820 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9830 ->
>>>>>>> origin/guido_tactics
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
<<<<<<< HEAD
      match uu____9701 with
=======
      match uu____9791 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                let uu____9828 = desugar_binders monad_env eff_binders in
                match uu____9828 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9841 =
                        let uu____9842 =
                          let uu____9846 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9846 in
                        FStar_List.length uu____9842 in
                      uu____9841 = (Prims.parse_int "1") in
=======
                let uu____9908 = desugar_binders monad_env eff_binders in
                match uu____9908 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9921 =
                        let uu____9922 =
                          let uu____9926 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9926 in
                        FStar_List.length uu____9922 in
                      uu____9921 = (Prims.parse_int "1") in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                          (uu____9874,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9876,uu____9877,uu____9878),uu____9879)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9896 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9897 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9905 = name_of_eff_decl decl in
                           FStar_List.mem uu____9905 mandatory_members)
                        eff_decls in
                    (match uu____9897 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9915 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9934  ->
                                   fun decl  ->
                                     match uu____9934 with
                                     | (env2,out) ->
                                         let uu____9946 =
                                           desugar_decl env2 decl in
                                         (match uu____9946 with
                                          | (env3,ses) ->
                                              let uu____9954 =
                                                let uu____9956 =
                                                  FStar_List.hd ses in
                                                uu____9956 :: out in
                                              (env3, uu____9954))) (env1, [])) in
                         (match uu____9915 with
=======
                          (uu____9957,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9959,uu____9960,uu____9961),uu____9962)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9979 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9980 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9986 = name_of_eff_decl decl in
                           FStar_List.mem uu____9986 mandatory_members)
                        eff_decls in
                    (match uu____9980 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9996 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____10007  ->
                                   fun decl  ->
                                     match uu____10007 with
                                     | (env2,out) ->
                                         let uu____10019 =
                                           desugar_decl env2 decl in
                                         (match uu____10019 with
                                          | (env3,ses) ->
                                              let uu____10027 =
                                                let uu____10029 =
                                                  FStar_List.hd ses in
                                                uu____10029 :: out in
                                              (env3, uu____10027)))
                                (env1, [])) in
                         (match uu____9996 with
>>>>>>> origin/guido_tactics
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
<<<<<<< HEAD
                                            (uu____10002,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10005,
=======
                                            (uu____10057,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10060,
>>>>>>> origin/guido_tactics
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
<<<<<<< HEAD
                                                               (uu____10006,
                                                                (def,uu____10008)::
                                                                (cps_type,uu____10010)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10011;
                                                             FStar_Parser_AST.level
                                                               = uu____10012;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10039 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10039 with
=======
                                                               (uu____10061,
                                                                (def,uu____10063)::
                                                                (cps_type,uu____10065)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10066;
                                                             FStar_Parser_AST.level
                                                               = uu____10067;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10094 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10094 with
>>>>>>> origin/guido_tactics
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
<<<<<<< HEAD
                                                 let uu____10051 =
                                                   let uu____10052 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10053 =
                                                     let uu____10054 =
=======
                                                 let uu____10106 =
                                                   let uu____10107 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10108 =
                                                     let uu____10109 =
>>>>>>> origin/guido_tactics
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____10054 in
                                                   let uu____10057 =
                                                     let uu____10058 =
=======
                                                       uu____10109 in
                                                   let uu____10112 =
                                                     let uu____10113 =
>>>>>>> origin/guido_tactics
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____10058 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10052;
=======
                                                       uu____10113 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10107;
>>>>>>> origin/guido_tactics
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
<<<<<<< HEAD
                                                       = uu____10053;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10057
                                                   } in
                                                 (uu____10051, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10062,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10065,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10084 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10084 with
=======
                                                       = uu____10108;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10112
                                                   } in
                                                 (uu____10106, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10117,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10120,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10139 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10139 with
>>>>>>> origin/guido_tactics
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
<<<<<<< HEAD
                                                 let uu____10096 =
                                                   let uu____10097 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10098 =
                                                     let uu____10099 =
=======
                                                 let uu____10151 =
                                                   let uu____10152 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10153 =
                                                     let uu____10154 =
>>>>>>> origin/guido_tactics
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
<<<<<<< HEAD
                                                       uu____10099 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10097;
=======
                                                       uu____10154 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10152;
>>>>>>> origin/guido_tactics
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
<<<<<<< HEAD
                                                       = uu____10098;
=======
                                                       = uu____10153;
>>>>>>> origin/guido_tactics
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
<<<<<<< HEAD
                                                 (uu____10096, doc1))
                                        | uu____10103 ->
=======
                                                 (uu____10151, doc1))
                                        | uu____10158 ->
>>>>>>> origin/guido_tactics
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let actions1 =
                                FStar_List.map FStar_Pervasives.fst
                                  actions_docs in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
<<<<<<< HEAD
                                let uu____10122 =
                                  let uu____10123 =
=======
                                let uu____10177 =
                                  let uu____10178 =
>>>>>>> origin/guido_tactics
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
<<<<<<< HEAD
                                    uu____10123 in
                                ([], uu____10122) in
=======
                                    uu____10178 in
                                ([], uu____10177) in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                    let uu____10135 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10135) in
                                  let uu____10145 =
                                    let uu____10146 =
                                      let uu____10147 =
                                        let uu____10148 = lookup "repr" in
                                        snd uu____10148 in
                                      let uu____10153 = lookup "return" in
                                      let uu____10154 = lookup "bind" in
=======
                                    let uu____10190 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10190) in
                                  let uu____10200 =
                                    let uu____10201 =
                                      let uu____10202 =
                                        let uu____10203 = lookup "repr" in
                                        snd uu____10203 in
                                      let uu____10208 = lookup "return" in
                                      let uu____10209 = lookup "bind" in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                          uu____10147;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10153;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10154;
=======
                                          uu____10202;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10208;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10209;
>>>>>>> origin/guido_tactics
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
<<<<<<< HEAD
                                      uu____10146 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10145;
=======
                                      uu____10201 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10200;
>>>>>>> origin/guido_tactics
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
<<<<<<< HEAD
                                       (fun uu___220_10158  ->
                                          match uu___220_10158 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10159 -> true
                                          | uu____10160 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10166 =
                                     let uu____10167 =
                                       let uu____10168 = lookup "return_wp" in
                                       let uu____10169 = lookup "bind_wp" in
                                       let uu____10170 =
                                         lookup "if_then_else" in
                                       let uu____10171 = lookup "ite_wp" in
                                       let uu____10172 = lookup "stronger" in
                                       let uu____10173 = lookup "close_wp" in
                                       let uu____10174 = lookup "assert_p" in
                                       let uu____10175 = lookup "assume_p" in
                                       let uu____10176 = lookup "null_wp" in
                                       let uu____10177 = lookup "trivial" in
                                       let uu____10178 =
                                         if rr
                                         then
                                           let uu____10179 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10179
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10188 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10190 =
=======
                                       (fun uu___222_10212  ->
                                          match uu___222_10212 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10213 -> true
                                          | uu____10214 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10220 =
                                     let uu____10221 =
                                       let uu____10222 = lookup "return_wp" in
                                       let uu____10223 = lookup "bind_wp" in
                                       let uu____10224 =
                                         lookup "if_then_else" in
                                       let uu____10225 = lookup "ite_wp" in
                                       let uu____10226 = lookup "stronger" in
                                       let uu____10227 = lookup "close_wp" in
                                       let uu____10228 = lookup "assert_p" in
                                       let uu____10229 = lookup "assume_p" in
                                       let uu____10230 = lookup "null_wp" in
                                       let uu____10231 = lookup "trivial" in
                                       let uu____10232 =
                                         if rr
                                         then
                                           let uu____10233 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10233
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10242 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10244 =
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                           uu____10168;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10169;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10170;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10171;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10172;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10173;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10174;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10175;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10176;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10177;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10178;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10188;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10190;
=======
                                           uu____10222;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10223;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10224;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10225;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10226;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10227;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10228;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10229;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10230;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10231;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10232;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10242;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10244;
>>>>>>> origin/guido_tactics
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
<<<<<<< HEAD
                                       uu____10167 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10166;
=======
                                       uu____10221 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10220;
>>>>>>> origin/guido_tactics
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
                                        fun uu____10208  ->
                                          match uu____10208 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10217 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10217 in
=======
                                        fun uu____10257  ->
                                          match uu____10257 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10266 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10266 in
>>>>>>> origin/guido_tactics
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
<<<<<<< HEAD
                                let uu____10219 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10219
=======
                                let uu____10268 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10268
>>>>>>> origin/guido_tactics
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
                                        FStar_Syntax_Syntax.default_sigmeta
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
      (FStar_Ident.lident option ->
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
<<<<<<< HEAD
                let uu____10244 = desugar_binders env1 eff_binders in
                match uu____10244 with
                | (env2,binders) ->
                    let uu____10255 =
                      let uu____10265 = head_and_args defn in
                      match uu____10265 with
=======
                let uu____10293 = desugar_binders env1 eff_binders in
                match uu____10293 with
                | (env2,binders) ->
                    let uu____10304 =
                      let uu____10314 = head_and_args defn in
                      match uu____10314 with
>>>>>>> origin/guido_tactics
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
<<<<<<< HEAD
                            | uu____10290 ->
                                let uu____10291 =
                                  let uu____10292 =
                                    let uu____10295 =
                                      let uu____10296 =
                                        let uu____10297 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10297 " not found" in
                                      Prims.strcat "Effect " uu____10296 in
                                    (uu____10295,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10292 in
                                raise uu____10291 in
=======
                            | uu____10339 ->
                                let uu____10340 =
                                  let uu____10341 =
                                    let uu____10344 =
                                      let uu____10345 =
                                        let uu____10346 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10346 " not found" in
                                      Prims.strcat "Effect " uu____10345 in
                                    (uu____10344,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10341 in
                                raise uu____10340 in
>>>>>>> origin/guido_tactics
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
<<<<<<< HEAD
                          let uu____10299 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10315)::args_rev ->
                                let uu____10322 =
                                  let uu____10323 = unparen last_arg in
                                  uu____10323.FStar_Parser_AST.tm in
                                (match uu____10322 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10338 -> ([], args))
                            | uu____10343 -> ([], args) in
                          (match uu____10299 with
                           | (cattributes,args1) ->
                               let uu____10370 = desugar_args env2 args1 in
                               let uu____10375 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10370, uu____10375)) in
                    (match uu____10255 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10409 =
                           match uu____10409 with
                           | (uu____10416,x) ->
                               let uu____10420 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10420 with
=======
                          let uu____10348 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10364)::args_rev ->
                                let uu____10371 =
                                  let uu____10372 = unparen last_arg in
                                  uu____10372.FStar_Parser_AST.tm in
                                (match uu____10371 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10387 -> ([], args))
                            | uu____10392 -> ([], args) in
                          (match uu____10348 with
                           | (cattributes,args1) ->
                               let uu____10419 = desugar_args env2 args1 in
                               let uu____10424 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10419, uu____10424)) in
                    (match uu____10304 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10458 =
                           match uu____10458 with
                           | (uu____10465,x) ->
                               let uu____10469 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10469 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                      let uu____10440 =
                                        let uu____10441 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10441 in
                                      ([], uu____10440)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10445 =
                             let uu____10446 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10446 in
                           let uu____10452 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10453 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10454 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10455 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10456 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10457 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10458 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10459 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10460 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10461 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10462 =
                             let uu____10463 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10463 in
                           let uu____10469 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10470 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10471 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10478 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10479 =
                                    let uu____10480 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10480 in
                                  let uu____10486 =
                                    let uu____10487 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10487 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10478;
=======
                                      let uu____10493 =
                                        let uu____10494 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10494 in
                                      ([], uu____10493)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10498 =
                             let uu____10499 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10499 in
                           let uu____10505 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10506 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10507 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10508 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10509 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10510 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10511 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10512 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10513 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10514 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10515 =
                             let uu____10516 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10516 in
                           let uu____10522 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10523 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10524 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10527 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10528 =
                                    let uu____10529 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10529 in
                                  let uu____10535 =
                                    let uu____10536 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10536 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10527;
>>>>>>> origin/guido_tactics
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
<<<<<<< HEAD
                                      uu____10479;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10486
=======
                                      uu____10528;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10535
>>>>>>> origin/guido_tactics
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
<<<<<<< HEAD
                             FStar_Syntax_Syntax.signature = uu____10445;
                             FStar_Syntax_Syntax.ret_wp = uu____10452;
                             FStar_Syntax_Syntax.bind_wp = uu____10453;
                             FStar_Syntax_Syntax.if_then_else = uu____10454;
                             FStar_Syntax_Syntax.ite_wp = uu____10455;
                             FStar_Syntax_Syntax.stronger = uu____10456;
                             FStar_Syntax_Syntax.close_wp = uu____10457;
                             FStar_Syntax_Syntax.assert_p = uu____10458;
                             FStar_Syntax_Syntax.assume_p = uu____10459;
                             FStar_Syntax_Syntax.null_wp = uu____10460;
                             FStar_Syntax_Syntax.trivial = uu____10461;
                             FStar_Syntax_Syntax.repr = uu____10462;
                             FStar_Syntax_Syntax.return_repr = uu____10469;
                             FStar_Syntax_Syntax.bind_repr = uu____10470;
                             FStar_Syntax_Syntax.actions = uu____10471
                           } in
                         let se =
                           let for_free =
                             let uu____10495 =
                               let uu____10496 =
                                 let uu____10500 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10500 in
                               FStar_List.length uu____10496 in
                             uu____10495 = (Prims.parse_int "1") in
                           let uu____10518 =
                             let uu____10520 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10520 quals in
=======
                             FStar_Syntax_Syntax.signature = uu____10498;
                             FStar_Syntax_Syntax.ret_wp = uu____10505;
                             FStar_Syntax_Syntax.bind_wp = uu____10506;
                             FStar_Syntax_Syntax.if_then_else = uu____10507;
                             FStar_Syntax_Syntax.ite_wp = uu____10508;
                             FStar_Syntax_Syntax.stronger = uu____10509;
                             FStar_Syntax_Syntax.close_wp = uu____10510;
                             FStar_Syntax_Syntax.assert_p = uu____10511;
                             FStar_Syntax_Syntax.assume_p = uu____10512;
                             FStar_Syntax_Syntax.null_wp = uu____10513;
                             FStar_Syntax_Syntax.trivial = uu____10514;
                             FStar_Syntax_Syntax.repr = uu____10515;
                             FStar_Syntax_Syntax.return_repr = uu____10522;
                             FStar_Syntax_Syntax.bind_repr = uu____10523;
                             FStar_Syntax_Syntax.actions = uu____10524
                           } in
                         let se =
                           let for_free =
                             let uu____10544 =
                               let uu____10545 =
                                 let uu____10549 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10549 in
                               FStar_List.length uu____10545 in
                             uu____10544 = (Prims.parse_int "1") in
                           let uu____10570 =
                             let uu____10572 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10572 quals in
>>>>>>> origin/guido_tactics
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
<<<<<<< HEAD
                             FStar_Syntax_Syntax.sigquals = uu____10518;
=======
                             FStar_Syntax_Syntax.sigquals = uu____10570;
>>>>>>> origin/guido_tactics
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
                                       let uu____10538 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10538 in
=======
                                       let uu____10586 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10586 in
>>>>>>> origin/guido_tactics
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
<<<<<<< HEAD
                           let uu____10540 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10540
=======
                           let uu____10588 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10588
>>>>>>> origin/guido_tactics
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
                                   FStar_Syntax_Syntax.default_sigmeta
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
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
<<<<<<< HEAD
      | FStar_Parser_AST.Fsdoc uu____10567 -> (env, [])
=======
      | FStar_Parser_AST.Fsdoc uu____10615 -> (env, [])
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
<<<<<<< HEAD
          let uu____10579 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10579, [])
=======
          let uu____10627 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10627, [])
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
<<<<<<< HEAD
              (fun uu____10603  ->
                 match uu____10603 with | (x,uu____10608) -> x) tcs in
          let uu____10611 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10611 tcs1
=======
              (fun uu____10648  ->
                 match uu____10648 with | (x,uu____10653) -> x) tcs in
          let uu____10656 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10656 tcs1
>>>>>>> origin/guido_tactics
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
<<<<<<< HEAD
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10629;
                    FStar_Parser_AST.prange = uu____10630;_},uu____10631)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10636;
                    FStar_Parser_AST.prange = uu____10637;_},uu____10638)::[]
=======
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10671;
                    FStar_Parser_AST.prange = uu____10672;_},uu____10673)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10678;
                    FStar_Parser_AST.prange = uu____10679;_},uu____10680)::[]
>>>>>>> origin/guido_tactics
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
<<<<<<< HEAD
                           uu____10646;
                         FStar_Parser_AST.prange = uu____10647;_},uu____10648);
                    FStar_Parser_AST.prange = uu____10649;_},uu____10650)::[]
                   -> false
               | (p,uu____10659)::[] ->
                   let uu____10664 = is_app_pattern p in
                   Prims.op_Negation uu____10664
               | uu____10665 -> false) in
=======
                           uu____10688;
                         FStar_Parser_AST.prange = uu____10689;_},uu____10690);
                    FStar_Parser_AST.prange = uu____10691;_},uu____10692)::[]
                   -> false
               | (p,uu____10701)::[] ->
                   let uu____10706 = is_app_pattern p in
                   Prims.op_Negation uu____10706
               | uu____10707 -> false) in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            let uu____10676 =
              let uu____10677 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10677.FStar_Syntax_Syntax.n in
            (match uu____10676 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10683) ->
=======
            let uu____10718 =
              let uu____10719 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10719.FStar_Syntax_Syntax.n in
            (match uu____10718 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10725) ->
>>>>>>> origin/guido_tactics
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
<<<<<<< HEAD
                   | uu____10704::uu____10705 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10707 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___221_10717  ->
                               match uu___221_10717 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10719;
                                   FStar_Syntax_Syntax.lbunivs = uu____10720;
                                   FStar_Syntax_Syntax.lbtyp = uu____10721;
                                   FStar_Syntax_Syntax.lbeff = uu____10722;
                                   FStar_Syntax_Syntax.lbdef = uu____10723;_}
=======
                   | uu____10745::uu____10746 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10748 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___223_10752  ->
                               match uu___223_10752 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10754;
                                   FStar_Syntax_Syntax.lbunivs = uu____10755;
                                   FStar_Syntax_Syntax.lbtyp = uu____10756;
                                   FStar_Syntax_Syntax.lbeff = uu____10757;
                                   FStar_Syntax_Syntax.lbdef = uu____10758;_}
>>>>>>> origin/guido_tactics
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
<<<<<<< HEAD
                                   FStar_Syntax_Syntax.lbunivs = uu____10730;
                                   FStar_Syntax_Syntax.lbtyp = uu____10731;
                                   FStar_Syntax_Syntax.lbeff = uu____10732;
                                   FStar_Syntax_Syntax.lbdef = uu____10733;_}
=======
                                   FStar_Syntax_Syntax.lbunivs = uu____10765;
                                   FStar_Syntax_Syntax.lbtyp = uu____10766;
                                   FStar_Syntax_Syntax.lbeff = uu____10767;
                                   FStar_Syntax_Syntax.lbdef = uu____10768;_}
>>>>>>> origin/guido_tactics
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
<<<<<<< HEAD
                   let uu____10741 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10750  ->
                             match uu____10750 with
                             | (uu____10753,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10741
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10761 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10761
                   then
                     let uu____10766 =
=======
                   let uu____10780 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10786  ->
                             match uu____10786 with
                             | (uu____10789,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10780
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10797 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10797
                   then
                     let uu____10802 =
>>>>>>> origin/guido_tactics
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
<<<<<<< HEAD
                               let uu___240_10776 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___241_10778 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___241_10778.FStar_Syntax_Syntax.fv_name);
=======
                               let uu___242_10809 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___243_10810 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___243_10810.FStar_Syntax_Syntax.fv_name);
>>>>>>> origin/guido_tactics
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
<<<<<<< HEAD
                                           (uu___241_10778.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10766)
=======
                                           (uu___243_10810.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___242_10809.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___242_10809.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___242_10809.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___242_10809.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10802)
>>>>>>> origin/guido_tactics
                   else lbs in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta
                   } in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names1 in
                 (env2, [s])
<<<<<<< HEAD
             | uu____10801 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10805 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10816 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10805 with
=======
             | uu____10837 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10841 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10852 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10841 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                       let uu___242_10832 = pat1 in
=======
                       let uu___244_10868 = pat1 in
>>>>>>> origin/guido_tactics
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
<<<<<<< HEAD
                           (uu___242_10832.FStar_Parser_AST.prange)
                       }
                   | uu____10833 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___243_10838 = d in
=======
                           (uu___244_10868.FStar_Parser_AST.prange)
                       }
                   | uu____10869 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___245_10873 = d in
>>>>>>> origin/guido_tactics
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
<<<<<<< HEAD
                          (uu___243_10838.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___243_10838.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___243_10838.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10857 id =
                   match uu____10857 with
                   | (env1,ses) ->
                       let main =
                         let uu____10870 =
                           let uu____10871 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10871 in
                         FStar_Parser_AST.mk_term uu____10870
=======
                          (uu___245_10873.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___245_10873.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___245_10873.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10892 id =
                   match uu____10892 with
                   | (env1,ses) ->
                       let main =
                         let uu____10905 =
                           let uu____10906 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10906 in
                         FStar_Parser_AST.mk_term uu____10905
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                       let uu____10899 = desugar_decl env1 id_decl in
                       (match uu____10899 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10910 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10910 FStar_Util.set_elements in
=======
                       let uu____10934 = desugar_decl env1 id_decl in
                       (match uu____10934 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10945 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10945 FStar_Util.set_elements in
>>>>>>> origin/guido_tactics
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
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
                 FStar_Syntax_Syntax.default_sigmeta
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
<<<<<<< HEAD
            let uu____10932 = close_fun env t in desugar_term env uu____10932 in
          let quals1 =
            let uu____10935 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10935
=======
            let uu____10966 = close_fun env t in desugar_term env uu____10966 in
          let quals1 =
            let uu____10969 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10969
>>>>>>> origin/guido_tactics
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
<<<<<<< HEAD
            let uu____10940 = FStar_List.map (trans_qual1 None) quals1 in
=======
            let uu____10974 = FStar_List.map (trans_qual1 None) quals1 in
>>>>>>> origin/guido_tactics
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
<<<<<<< HEAD
              FStar_Syntax_Syntax.sigquals = uu____10940;
=======
              FStar_Syntax_Syntax.sigquals = uu____10974;
>>>>>>> origin/guido_tactics
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
<<<<<<< HEAD
          let uu____10948 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10948 with
           | (t,uu____10956) ->
=======
          let uu____10982 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10982 with
           | (t,uu____10990) ->
>>>>>>> origin/guido_tactics
               let l = FStar_ToSyntax_Env.qualify env id in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
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
                     FStar_Syntax_Syntax.default_sigmeta
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta
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
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t1 =
<<<<<<< HEAD
            let uu____10981 =
              let uu____10985 = FStar_Syntax_Syntax.null_binder t in
              [uu____10985] in
            let uu____10986 =
              let uu____10989 =
                let uu____10990 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10990 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10989 in
            FStar_Syntax_Util.arrow uu____10981 uu____10986 in
=======
            let uu____11015 =
              let uu____11019 = FStar_Syntax_Syntax.null_binder t in
              [uu____11019] in
            let uu____11020 =
              let uu____11023 =
                let uu____11024 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____11024 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____11023 in
            FStar_Syntax_Util.arrow uu____11015 uu____11020 in
>>>>>>> origin/guido_tactics
          let l = FStar_ToSyntax_Env.qualify env id in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Syntax_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
            let uu____11034 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11034 with
            | None  ->
                let uu____11036 =
                  let uu____11037 =
                    let uu____11040 =
                      let uu____11041 =
                        let uu____11042 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11042 " not found" in
                      Prims.strcat "Effect name " uu____11041 in
                    (uu____11040, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11037 in
                raise uu____11036
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11046 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11068 =
                  let uu____11073 =
                    let uu____11077 = desugar_term env t in ([], uu____11077) in
                  Some uu____11073 in
                (uu____11068, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11095 =
                  let uu____11100 =
                    let uu____11104 = desugar_term env wp in
                    ([], uu____11104) in
                  Some uu____11100 in
                let uu____11109 =
                  let uu____11114 =
                    let uu____11118 = desugar_term env t in ([], uu____11118) in
                  Some uu____11114 in
                (uu____11095, uu____11109)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11132 =
                  let uu____11137 =
                    let uu____11141 = desugar_term env t in ([], uu____11141) in
                  Some uu____11137 in
                (None, uu____11132) in
          (match uu____11046 with
=======
            let uu____11068 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11068 with
            | None  ->
                let uu____11070 =
                  let uu____11071 =
                    let uu____11074 =
                      let uu____11075 =
                        let uu____11076 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11076 " not found" in
                      Prims.strcat "Effect name " uu____11075 in
                    (uu____11074, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11071 in
                raise uu____11070
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11080 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11102 =
                  let uu____11107 =
                    let uu____11111 = desugar_term env t in ([], uu____11111) in
                  Some uu____11107 in
                (uu____11102, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11129 =
                  let uu____11134 =
                    let uu____11138 = desugar_term env wp in
                    ([], uu____11138) in
                  Some uu____11134 in
                let uu____11143 =
                  let uu____11148 =
                    let uu____11152 = desugar_term env t in ([], uu____11152) in
                  Some uu____11148 in
                (uu____11129, uu____11143)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11166 =
                  let uu____11171 =
                    let uu____11175 = desugar_term env t in ([], uu____11175) in
                  Some uu____11171 in
                (None, uu____11166) in
          (match uu____11080 with
>>>>>>> origin/guido_tactics
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
                     FStar_Syntax_Syntax.default_sigmeta
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
<<<<<<< HEAD
        (fun uu____11199  ->
           fun d  ->
             match uu____11199 with
             | (env1,sigelts) ->
                 let uu____11211 = desugar_decl env1 d in
                 (match uu____11211 with
=======
        (fun uu____11228  ->
           fun d  ->
             match uu____11228 with
             | (env1,sigelts) ->
                 let uu____11240 = desugar_decl env1 d in
                 (match uu____11240 with
>>>>>>> origin/guido_tactics
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
  FStar_Syntax_Syntax.modul option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t* FStar_Syntax_Syntax.modul* Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
<<<<<<< HEAD
          | (None ,uu____11253) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11256;
               FStar_Syntax_Syntax.exports = uu____11257;
               FStar_Syntax_Syntax.is_interface = uu____11258;_},FStar_Parser_AST.Module
             (current_lid,uu____11260)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11265) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11267 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11287 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11287, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11297 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11297, mname, decls, false) in
        match uu____11267 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11315 = desugar_decls env2 decls in
            (match uu____11315 with
=======
          | (None ,uu____11285) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11288;
               FStar_Syntax_Syntax.exports = uu____11289;
               FStar_Syntax_Syntax.is_interface = uu____11290;_},FStar_Parser_AST.Module
             (current_lid,uu____11292)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11297) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11299 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11319 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11319, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11329 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11329, mname, decls, false) in
        match uu____11299 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11347 = desugar_decls env2 decls in
            (match uu____11347 with
>>>>>>> origin/guido_tactics
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
  FStar_Syntax_Syntax.modul option ->
    env_t -> FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
<<<<<<< HEAD
          let uu____11349 =
            (FStar_Options.interactive ()) &&
              (let uu____11351 =
                 let uu____11352 =
                   let uu____11353 = FStar_Options.file_list () in
                   FStar_List.hd uu____11353 in
                 FStar_Util.get_file_extension uu____11352 in
               uu____11351 = "fsti") in
          if uu____11349 then as_interface m else m in
        let uu____11356 = desugar_modul_common curmod env m1 in
        match uu____11356 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11366 = FStar_ToSyntax_Env.pop () in ())
=======
          let uu____11385 =
            (FStar_Options.interactive ()) &&
              (let uu____11386 =
                 let uu____11387 =
                   let uu____11388 = FStar_Options.file_list () in
                   FStar_List.hd uu____11388 in
                 FStar_Util.get_file_extension uu____11387 in
               uu____11386 = "fsti") in
          if uu____11385 then as_interface m else m in
        let uu____11391 = desugar_modul_common curmod env m1 in
        match uu____11391 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11401 = FStar_ToSyntax_Env.pop () in ())
>>>>>>> origin/guido_tactics
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
<<<<<<< HEAD
      let uu____11378 = desugar_modul_common None env m in
      match uu____11378 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11389 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11389
            then
              let uu____11390 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11390
            else ());
           (let uu____11392 =
=======
      let uu____11415 = desugar_modul_common None env m in
      match uu____11415 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11426 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11426
            then
              let uu____11427 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11427
            else ());
           (let uu____11429 =
>>>>>>> origin/guido_tactics
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
<<<<<<< HEAD
            (uu____11392, modul)))
=======
            (uu____11429, modul)))
>>>>>>> origin/guido_tactics
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
<<<<<<< HEAD
      let uu____11403 =
        FStar_List.fold_left
          (fun uu____11417  ->
             fun m  ->
               match uu____11417 with
               | (env1,mods) ->
                   let uu____11429 = desugar_modul env1 m in
                   (match uu____11429 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11403 with | (env1,mods) -> (env1, (FStar_List.rev mods))
=======
      let uu____11442 =
        FStar_List.fold_left
          (fun uu____11449  ->
             fun m  ->
               match uu____11449 with
               | (env1,mods) ->
                   let uu____11461 = desugar_modul env1 m in
                   (match uu____11461 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11442 with | (env1,mods) -> (env1, (FStar_List.rev mods))
>>>>>>> origin/guido_tactics
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
<<<<<<< HEAD
      let uu____11453 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11453 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11459 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11459
=======
      let uu____11487 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11487 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11493 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11493
>>>>>>> origin/guido_tactics
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env