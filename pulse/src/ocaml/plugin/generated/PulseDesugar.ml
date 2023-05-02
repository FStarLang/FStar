open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  dsenv: FStar_Syntax_DsEnv.env ;
  local_refs: FStar_Ident.ident Prims.list }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { tcenv; dsenv; local_refs;_} -> tcenv
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with | { tcenv; dsenv; local_refs;_} -> dsenv
let (__proj__Mkenv__item__local_refs : env -> FStar_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; dsenv; local_refs;_} -> local_refs
let (stapp_assignment :
  PulseSyntaxWrapper.term ->
    PulseSyntaxWrapper.term -> PulseSyntaxWrapper.st_term)
  = fun lhs -> fun rhs -> Prims.admit ()
let (resolve_name : env -> FStar_Ident.ident -> FStar_Syntax_Syntax.term) =
  fun env1 ->
    fun id ->
      let uu___ = FStar_Syntax_DsEnv.try_lookup_id env1.dsenv id in
      match uu___ with
      | FStar_Pervasives_Native.None -> failwith "Name not found"
      | FStar_Pervasives_Native.Some t -> t
let (stapp_or_return :
  env -> FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.st_term) =
  fun env1 -> fun s -> Prims.admit ()
let (desugar_term : env -> FStar_Parser_AST.term -> PulseSyntaxWrapper.term)
  =
  fun env1 ->
    fun t ->
      let uu___ = FStar_ToSyntax_ToSyntax.desugar_term env1.dsenv t in
      PulseSyntaxWrapper.tm_expr uu___
let (desugar_term_opt :
  env ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxWrapper.term)
  =
  fun env1 ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None -> PulseSyntaxWrapper.tm_unknown
      | FStar_Pervasives_Native.Some e -> desugar_term env1 e
let (desugar_vprop : env -> PulseSugar.vprop -> PulseSyntaxWrapper.vprop) =
  fun env1 -> fun v -> Prims.admit ()
let rec (desugar_stmt : env -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term)
  =
  fun env1 ->
    fun s ->
      match s.PulseSugar.s with
      | PulseSugar.Expr { PulseSugar.e = e;_} ->
          let tm = FStar_ToSyntax_ToSyntax.desugar_term env1.dsenv e in
          let uu___ = PulseSyntaxWrapper.tm_expr tm in
          PulseSyntaxWrapper.tm_return uu___
      | PulseSugar.Assignment
          { PulseSugar.id = id; PulseSugar.value = value;_} ->
          let lhs = resolve_name env1 id in
          let value1 = FStar_ToSyntax_ToSyntax.desugar_term env1.dsenv value in
          let uu___ = PulseSyntaxWrapper.tm_expr lhs in
          let uu___1 = PulseSyntaxWrapper.tm_expr value1 in
          stapp_assignment uu___ uu___1
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.LetBinding lb;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> desugar_bind env1 lb s2
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} ->
          desugar_sequence env1 s1 s2
      | PulseSugar.Block { PulseSugar.stmt = stmt;_} ->
          desugar_stmt env1 stmt
      | PulseSugar.If
          { PulseSugar.head1 = head; PulseSugar.join_vprop = join_vprop;
            PulseSugar.then_ = then_; PulseSugar.else_opt = else_opt;_}
          ->
          let head1 = desugar_term env1 head in
          let join_vprop1 =
            match join_vprop with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some t ->
                let uu___ = desugar_vprop env1 t in
                FStar_Pervasives_Native.Some uu___ in
          let then_1 = desugar_stmt env1 then_ in
          let else_ =
            match else_opt with
            | FStar_Pervasives_Native.None ->
                let uu___ =
                  PulseSyntaxWrapper.tm_expr FStar_Syntax_Syntax.unit_const in
                PulseSyntaxWrapper.tm_return uu___ in
          PulseSyntaxWrapper.tm_if head1 join_vprop1 then_1 else_
      | PulseSugar.Match
          { PulseSugar.head2 = head;
            PulseSugar.returns_annot = returns_annot;
            PulseSugar.branches = branches;_}
          -> failwith "Match is not yet handled"
      | PulseSugar.While
          { PulseSugar.head3 = head; PulseSugar.id2 = id;
            PulseSugar.invariant = invariant; PulseSugar.body1 = body;_}
          ->
          let head1 =
            let uu___ = FStar_ToSyntax_ToSyntax.desugar_term env1.dsenv head in
            stapp_or_return env1 uu___ in
          let invariant1 =
            let uu___ = FStar_Syntax_DsEnv.push_bv env1.dsenv id in
            match uu___ with
            | (dsenv, uu___1) ->
                let env2 =
                  {
                    tcenv = (env1.tcenv);
                    dsenv;
                    local_refs = (env1.local_refs)
                  } in
                desugar_vprop env2 invariant in
          let body1 = desugar_stmt env1 body in
          PulseSyntaxWrapper.tm_while head1 (id, invariant1) body1
      | PulseSugar.LetBinding uu___ -> failwith "Terminal let binding"
and (desugar_bind :
  env ->
    PulseSugar.stmt'__LetBinding__payload ->
      PulseSugar.stmt -> PulseSyntaxWrapper.st_term)
  =
  fun env1 ->
    fun lb ->
      fun s2 ->
        let annot = desugar_term_opt env1 lb.PulseSugar.typ in
        let s21 =
          let uu___ = FStar_Syntax_DsEnv.push_bv env1.dsenv lb.PulseSugar.id1 in
          match uu___ with
          | (dsenv, uu___1) ->
              let env2 =
                { tcenv = (env1.tcenv); dsenv; local_refs = (env1.local_refs)
                } in
              desugar_stmt env1 s2 in
        match lb.PulseSugar.init with
        | FStar_Pervasives_Native.None ->
            failwith "Uninitialized variables are not yet handled"
        | FStar_Pervasives_Native.Some e1 ->
            (match lb.PulseSugar.qualifier with
             | FStar_Pervasives_Native.None ->
                 let s1 =
                   let uu___ =
                     FStar_ToSyntax_ToSyntax.desugar_term env1.dsenv e1 in
                   stapp_or_return env1 uu___ in
                 PulseSyntaxWrapper.tm_bind
                   (FStar_Pervasives_Native.Some ((lb.PulseSugar.id1), annot))
                   s1 s21
             | FStar_Pervasives_Native.Some (PulseSugar.MUT) ->
                 let e11 = desugar_term env1 e1 in
                 PulseSyntaxWrapper.tm_let_mut lb.PulseSugar.id1 annot e11
                   s21
             | FStar_Pervasives_Native.Some (PulseSugar.REF) ->
                 let e11 = desugar_term env1 e1 in
                 PulseSyntaxWrapper.tm_let_mut lb.PulseSugar.id1 annot e11
                   s21)
and (desugar_sequence :
  env -> PulseSugar.stmt -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term) =
  fun env1 ->
    fun s1 ->
      fun s2 ->
        let s11 = desugar_stmt env1 s1 in
        let s21 = desugar_stmt env1 s2 in
        PulseSyntaxWrapper.tm_bind FStar_Pervasives_Native.None s11 s21
let (explicit_rvalues : env -> PulseSugar.stmt -> PulseSugar.stmt) =
  fun env1 -> fun s -> s
let (desugar_decl : PulseSugar.decl -> PulseSyntaxWrapper.st_term) =
  fun p -> Prims.admit ()