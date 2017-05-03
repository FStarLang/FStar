module FStar.Reflection.Interpreter

let x = 2
(*
      mk "__compare_binder" 2 (mk_pure_interpretation_2 order_binder E.unembed_binder E.unembed_binder E.embed_order);
      mk "__inspect" 1 (mk_pure_interpretation_1 E.inspect E.unembed_term E.embed_term_view);
      mk "__pack" 1 (mk_pure_interpretation_1 E.pack E.unembed_term_view E.embed_term);

      mk "__inspect_fv" 1 (mk_pure_interpretation_1 E.inspectfv E.unembed_fvar (E.embed_list E.embed_string FStar.TypeChecker.Common.t_string));
      mk "__pack_fv"    1 (mk_pure_interpretation_1 E.packfv (E.unembed_list E.unembed_string) E.embed_fvar);

      mk "__inspect_bv" 1 (mk_pure_interpretation_1 E.inspectbv E.unembed_binder E.embed_string);
      mk "__term_to_string"  1 (mk_pure_interpretation_1 Print.term_to_string E.unembed_term E.embed_string);



let binders_of_env ps (nm:Ident.lid) (args:S.args) =
  match args with
  | [(embedded_env, _)] ->
    let env = E.unembed_env ps.main_context embedded_env in
    Some (E.embed_binders (Env.all_binders env))
  | _ -> None

let type_of_binder (nm:Ident.lid) (args:S.args) =
  match args with
  | [(embedded_binder, _)] ->
    let b, _ = E.unembed_binder embedded_binder in
    Some (E.embed_term b.sort)
  | _ -> None

      mk "__binders_of_env"  1 (binders_of_env ps);
      mk "__type_of_binder"  1 type_of_binder;
      mk "__term_eq"         2 term_eq;

let quote (nm:Ident.lid) (args:S.args) =
  match args with
  | [_; (y, _)] -> Some (E.embed_term y)
  | _ -> None

      *)
