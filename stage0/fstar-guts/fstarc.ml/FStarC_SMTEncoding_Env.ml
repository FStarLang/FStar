open Prims
let dbg_PartialApp : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "PartialApp"
let add_fuel (x : 'uuuuu) (tl : 'uuuuu Prims.list) : 'uuuuu Prims.list=
  let uu___ = FStarC_Options.unthrottle_inductives () in
  if uu___ then tl else x :: tl
let withenv (c : 'uuuuu) (uu___ : ('uuuuu1 * 'uuuuu2)) :
  ('uuuuu1 * 'uuuuu2 * 'uuuuu)= match uu___ with | (a, b) -> (a, b, c)
let vargs
  (args : (('uuuuu, 'uuuuu1) FStar_Pervasives.either * 'uuuuu2) Prims.list) :
  (('uuuuu, 'uuuuu1) FStar_Pervasives.either * 'uuuuu2) Prims.list=
  FStarC_List.filter
    (fun uu___ ->
       match uu___ with
       | (FStar_Pervasives.Inl uu___1, uu___2) -> false
       | uu___1 -> true) args
let escape (s : Prims.string) : Prims.string=
  FStarC_Util.replace_char s 39 95
let mk_term_projector_name (lid : FStarC_Ident.lident)
  (a : FStarC_Syntax_Syntax.bv) : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid lid in
    let uu___2 = FStarC_Ident.string_of_id a.FStarC_Syntax_Syntax.ppname in
    FStarC_Format.fmt2 "%s_@%s" uu___1 uu___2 in
  escape uu___
let mk_univ_projector_name (lid : FStarC_Ident.lident) (i : Prims.int) :
  Prims.string=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid lid in
    FStarC_Format.fmt2 "%s_@%s" uu___1 (Prims.string_of_int i) in
  escape uu___
let primitive_projector_by_pos (env : FStarC_TypeChecker_Env.env)
  (lid : FStarC_Ident.lident) (i : Prims.int) : Prims.string=
  let fail uu___ =
    let uu___1 =
      let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let uu___3 = FStarC_Ident.string_of_lid lid in
      FStarC_Format.fmt2 "Projector %s on data constructor %s not found"
        uu___2 uu___3 in
    failwith uu___1 in
  let uu___ = FStarC_TypeChecker_Env.lookup_datacon env lid in
  match uu___ with
  | (uu___1, t) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress t in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_arrow
           { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_}
           ->
           let uu___3 = FStarC_Syntax_Subst.open_comp bs c in
           (match uu___3 with
            | (binders, uu___4) ->
                if
                  (i < Prims.int_zero) || (i >= (FStarC_List.length binders))
                then fail ()
                else
                  (let b = FStarC_List.nth binders i in
                   mk_term_projector_name lid
                     b.FStarC_Syntax_Syntax.binder_bv))
       | uu___3 -> fail ())
let mk_term_projector_name_by_pos (lid : FStarC_Ident.lident) (i : Prims.int)
  : Prims.string=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid lid in
    let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
    FStarC_Format.fmt2 "%s_@%s" uu___1 uu___2 in
  escape uu___
let mk_term_projector (lid : FStarC_Ident.lident)
  (a : FStarC_Syntax_Syntax.bv) : FStarC_SMTEncoding_Term.term=
  let uu___ =
    let uu___1 =
      let uu___2 = mk_term_projector_name lid a in
      (uu___2,
        (FStarC_SMTEncoding_Term.Arrow
           (FStarC_SMTEncoding_Term.Term_sort,
             FStarC_SMTEncoding_Term.Term_sort))) in
    FStarC_SMTEncoding_Term.mk_fv uu___1 in
  FStarC_SMTEncoding_Util.mkFreeV uu___
let mk_term_projector_by_pos (lid : FStarC_Ident.lident) (i : Prims.int) :
  FStarC_SMTEncoding_Term.term=
  let uu___ =
    let uu___1 =
      let uu___2 = mk_term_projector_name_by_pos lid i in
      (uu___2,
        (FStarC_SMTEncoding_Term.Arrow
           (FStarC_SMTEncoding_Term.Term_sort,
             FStarC_SMTEncoding_Term.Term_sort))) in
    FStarC_SMTEncoding_Term.mk_fv uu___1 in
  FStarC_SMTEncoding_Util.mkFreeV uu___
let mk_data_tester (env : 'uuuuu) (l : FStarC_Ident.lident)
  (x : FStarC_SMTEncoding_Term.term) : FStarC_SMTEncoding_Term.term=
  let uu___ = let uu___1 = FStarC_Ident.string_of_lid l in escape uu___1 in
  FStarC_SMTEncoding_Term.mk_tester uu___ x
type varops_t =
  {
  push: unit -> unit ;
  pop: unit -> unit ;
  snapshot: unit -> (Prims.int * unit) ;
  rollback: Prims.int FStar_Pervasives_Native.option -> unit ;
  new_var: FStarC_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStarC_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string -> Prims.string ;
  reset_fresh: unit -> unit ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string ;
  reset_scope: unit -> unit }
let __proj__Mkvarops_t__item__push (projectee : varops_t) : unit -> unit=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> push
let __proj__Mkvarops_t__item__pop (projectee : varops_t) : unit -> unit=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> pop
let __proj__Mkvarops_t__item__snapshot (projectee : varops_t) :
  unit -> (Prims.int * unit)=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> snapshot
let __proj__Mkvarops_t__item__rollback (projectee : varops_t) :
  Prims.int FStar_Pervasives_Native.option -> unit=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> rollback
let __proj__Mkvarops_t__item__new_var (projectee : varops_t) :
  FStarC_Ident.ident -> Prims.int -> Prims.string=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> new_var
let __proj__Mkvarops_t__item__new_fvar (projectee : varops_t) :
  FStarC_Ident.lident -> Prims.string=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> new_fvar
let __proj__Mkvarops_t__item__fresh (projectee : varops_t) :
  Prims.string -> Prims.string -> Prims.string=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> fresh
let __proj__Mkvarops_t__item__reset_fresh (projectee : varops_t) :
  unit -> unit=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> reset_fresh
let __proj__Mkvarops_t__item__next_id (projectee : varops_t) :
  unit -> Prims.int=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> next_id
let __proj__Mkvarops_t__item__mk_unique (projectee : varops_t) :
  Prims.string -> Prims.string=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> mk_unique
let __proj__Mkvarops_t__item__reset_scope (projectee : varops_t) :
  unit -> unit=
  match projectee with
  | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
      next_id; mk_unique; reset_scope;_} -> reset_scope
let varops : varops_t=
  let initial_ctr = (Prims.of_int (100)) in
  let ctr = FStarC_Effect.mk_ref initial_ctr in
  let new_scope uu___ = FStarC_SMap.create (Prims.of_int (100)) in
  let scopes =
    let uu___ = let uu___1 = new_scope () in [uu___1] in
    FStarC_Effect.mk_ref uu___ in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu___ =
        let uu___1 = FStarC_Effect.op_Bang scopes in
        FStarC_Util.find_map uu___1
          (fun names -> FStarC_SMap.try_find names y1) in
      match uu___ with
      | FStar_Pervasives_Native.None -> y1
      | FStar_Pervasives_Native.Some uu___1 ->
          (FStarC_Util.incr ctr;
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Effect.op_Bang ctr in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___5 in
              Prims.strcat "__" uu___4 in
            Prims.strcat y1 uu___3)) in
    let top_scope =
      let uu___ = FStarC_Effect.op_Bang scopes in FStarC_List.hd uu___ in
    FStarC_SMap.add top_scope y2 true; y2 in
  let new_var pp rn =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_id pp in
      let uu___2 =
        let uu___3 = FStarC_Class_Show.show FStarC_Class_Show.showable_int rn in
        Prims.strcat "__" uu___3 in
      Prims.strcat uu___1 uu___2 in
    mk_unique uu___ in
  let new_fvar lid =
    let uu___ = FStarC_Ident.string_of_lid lid in mk_unique uu___ in
  let next_id uu___ = FStarC_Util.incr ctr; FStarC_Effect.op_Bang ctr in
  let fresh mname pfx =
    let uu___ =
      let uu___1 = next_id () in
      FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___1 in
    FStarC_Format.fmt3 "%s_%s_%s" pfx mname uu___ in
  let reset_fresh uu___ = FStarC_Effect.op_Colon_Equals ctr initial_ctr in
  let push uu___ =
    (let uu___2 = FStarC_Debug.any () in
     if uu___2
     then FStarC_Format.print_string "SMTEncoding.scopes.push\n"
     else ());
    (let uu___2 =
       let uu___3 = new_scope () in
       let uu___4 = FStarC_Effect.op_Bang scopes in uu___3 :: uu___4 in
     FStarC_Effect.op_Colon_Equals scopes uu___2) in
  let pop uu___ =
    (let uu___2 = FStarC_Debug.any () in
     if uu___2
     then FStarC_Format.print_string "SMTEncoding.scopes.pop\n"
     else ());
    (let uu___2 =
       let uu___3 = FStarC_Effect.op_Bang scopes in FStarC_List.tl uu___3 in
     FStarC_Effect.op_Colon_Equals scopes uu___2) in
  let snapshot uu___ =
    FStarC_Common.snapshot "SMTEncoding.scopes" push scopes () in
  let rollback depth =
    FStarC_Common.rollback "SMTEncoding.scopes" pop scopes depth in
  {
    push;
    pop;
    snapshot;
    rollback;
    new_var;
    new_fvar;
    fresh;
    reset_fresh;
    next_id;
    mk_unique;
    reset_scope =
      (fun uu___ ->
         (let uu___2 = FStarC_Debug.any () in
          if uu___2 then FStarC_Format.print_string "reset_scope!\n" else ());
         (let uu___2 = let uu___3 = new_scope () in [uu___3] in
          FStarC_Effect.op_Colon_Equals scopes uu___2))
  }
type fvar_binding =
  {
  fvar_lid: FStarC_Ident.lident ;
  univ_arity: Prims.int ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
      FStar_Pervasives_Native.option
    ;
  fvb_thunked: Prims.bool ;
  needs_fuel_and_universe_instantiations:
    FStarC_Syntax_Syntax.univ_names FStar_Pervasives_Native.option }
let __proj__Mkfvar_binding__item__fvar_lid (projectee : fvar_binding) :
  FStarC_Ident.lident=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> fvar_lid
let __proj__Mkfvar_binding__item__univ_arity (projectee : fvar_binding) :
  Prims.int=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> univ_arity
let __proj__Mkfvar_binding__item__smt_arity (projectee : fvar_binding) :
  Prims.int=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> smt_arity
let __proj__Mkfvar_binding__item__smt_id (projectee : fvar_binding) :
  Prims.string=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> smt_id
let __proj__Mkfvar_binding__item__smt_token (projectee : fvar_binding) :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> smt_token
let __proj__Mkfvar_binding__item__smt_fuel_partial_app
  (projectee : fvar_binding) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
    FStar_Pervasives_Native.option=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> smt_fuel_partial_app
let __proj__Mkfvar_binding__item__fvb_thunked (projectee : fvar_binding) :
  Prims.bool=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} -> fvb_thunked
let __proj__Mkfvar_binding__item__needs_fuel_and_universe_instantiations
  (projectee : fvar_binding) :
  FStarC_Syntax_Syntax.univ_names FStar_Pervasives_Native.option=
  match projectee with
  | { fvar_lid; univ_arity; smt_arity; smt_id; smt_token;
      smt_fuel_partial_app; fvb_thunked;
      needs_fuel_and_universe_instantiations;_} ->
      needs_fuel_and_universe_instantiations
let list_of (i : Prims.int) (f : Prims.int -> 'a) : 'a Prims.list=
  let rec aux i1 out =
    if i1 = Prims.int_zero
    then let uu___ = f i1 in uu___ :: out
    else
      (let uu___1 = let uu___2 = f i1 in uu___2 :: out in
       aux (i1 - Prims.int_one) uu___1) in
  if i <= Prims.int_zero then [] else aux (i - Prims.int_one) []
let kick_partial_app (fvb : fvar_binding) :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option=
  match ((fvb.smt_token), (fvb.needs_fuel_and_universe_instantiations)) with
  | (FStar_Pervasives_Native.None, uu___) -> FStar_Pervasives_Native.None
  | (uu___, FStar_Pervasives_Native.Some uu___1) ->
      FStar_Pervasives_Native.None
  | (FStar_Pervasives_Native.Some
     {
       FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.FreeV
         (FStarC_SMTEncoding_Term.FV (tok, uu___, uu___1));
       FStarC_SMTEncoding_Term.freevars = uu___2;
       FStarC_SMTEncoding_Term.rng = uu___3;_},
     uu___4) ->
      if fvb.univ_arity = Prims.int_zero
      then
        let t = FStarC_SMTEncoding_Util.mkApp (tok, []) in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              FStarC_SMTEncoding_Util.mkApp ("__uu__PartialApp", []) in
            FStarC_SMTEncoding_Util.mk_ApplyTT uu___7 t in
          FStarC_SMTEncoding_Term.mk_Valid uu___6 in
        FStar_Pervasives_Native.Some uu___5
      else
        (let vars =
           list_of (fvb.smt_arity + fvb.univ_arity)
             (fun i ->
                let sort =
                  if i < fvb.univ_arity
                  then FStarC_SMTEncoding_Term.univ_sort
                  else FStarC_SMTEncoding_Term.Term_sort in
                FStarC_SMTEncoding_Term.mk_fv
                  ((Prims.strcat "@u" (Prims.string_of_int i)), sort)) in
         let var_terms = FStarC_List.map FStarC_SMTEncoding_Util.mkFreeV vars in
         let vapp = FStarC_SMTEncoding_Util.mkApp ((fvb.smt_id), var_terms) in
         let uu___6 = FStarC_List.splitAt fvb.univ_arity var_terms in
         match uu___6 with
         | (univs, rest) ->
             let vtok_app =
               let uu___7 = FStarC_SMTEncoding_Util.mkApp (tok, univs) in
               FStarC_List.fold_left FStarC_SMTEncoding_Util.mk_ApplyTT
                 uu___7 rest in
             let uu___7 =
               let uu___8 =
                 let uu___9 = FStarC_SMTEncoding_Util.mkEq (vapp, vtok_app) in
                 ([[vapp]], vars, uu___9) in
               FStarC_SMTEncoding_Term.mkForall FStarC_Range_Type.dummyRange
                 uu___8 in
             FStar_Pervasives_Native.Some uu___7)
  | (FStar_Pervasives_Native.Some
     {
       FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var tok, uu___);
       FStarC_SMTEncoding_Term.freevars = uu___1;
       FStarC_SMTEncoding_Term.rng = uu___2;_},
     uu___3) ->
      if fvb.univ_arity = Prims.int_zero
      then
        let t = FStarC_SMTEncoding_Util.mkApp (tok, []) in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_SMTEncoding_Util.mkApp ("__uu__PartialApp", []) in
            FStarC_SMTEncoding_Util.mk_ApplyTT uu___6 t in
          FStarC_SMTEncoding_Term.mk_Valid uu___5 in
        FStar_Pervasives_Native.Some uu___4
      else
        (let vars =
           list_of (fvb.smt_arity + fvb.univ_arity)
             (fun i ->
                let sort =
                  if i < fvb.univ_arity
                  then FStarC_SMTEncoding_Term.univ_sort
                  else FStarC_SMTEncoding_Term.Term_sort in
                FStarC_SMTEncoding_Term.mk_fv
                  ((Prims.strcat "@u" (Prims.string_of_int i)), sort)) in
         let var_terms = FStarC_List.map FStarC_SMTEncoding_Util.mkFreeV vars in
         let vapp = FStarC_SMTEncoding_Util.mkApp ((fvb.smt_id), var_terms) in
         let uu___5 = FStarC_List.splitAt fvb.univ_arity var_terms in
         match uu___5 with
         | (univs, rest) ->
             let vtok_app =
               let uu___6 = FStarC_SMTEncoding_Util.mkApp (tok, univs) in
               FStarC_List.fold_left FStarC_SMTEncoding_Util.mk_ApplyTT
                 uu___6 rest in
             let uu___6 =
               let uu___7 =
                 let uu___8 = FStarC_SMTEncoding_Util.mkEq (vapp, vtok_app) in
                 ([[vapp]], vars, uu___8) in
               FStarC_SMTEncoding_Term.mkForall FStarC_Range_Type.dummyRange
                 uu___7 in
             FStar_Pervasives_Native.Some uu___6)
let fvb_to_string (fvb : fvar_binding) : Prims.string=
  let term_opt_to_string uu___ =
    match uu___ with
    | FStar_Pervasives_Native.None -> "None"
    | FStar_Pervasives_Native.Some s ->
        FStarC_SMTEncoding_Term.print_smt_term s in
  let term_pair_opt_to_string uu___ =
    match uu___ with
    | FStar_Pervasives_Native.None -> "None"
    | FStar_Pervasives_Native.Some (s0, s1) ->
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_tuple2
             FStarC_SMTEncoding_Term.showable_smt_term
             FStarC_SMTEncoding_Term.showable_smt_term) (s0, s1) in
  let uu___ =
    FStarC_Class_Show.show FStarC_Ident.showable_lident fvb.fvar_lid in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int fvb.smt_arity in
  let uu___2 = term_opt_to_string fvb.smt_token in
  let uu___3 = term_pair_opt_to_string fvb.smt_fuel_partial_app in
  let uu___4 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_bool fvb.fvb_thunked in
  FStarC_Format.fmt6
    "{ lid = %s;\n  smt_arity = %s;\n  smt_id = %s;\n  smt_token = %s;\n  smt_fuel_partial_app = %s;\n  fvb_thunked = %s }"
    uu___ uu___1 fvb.smt_id uu___2 uu___3 uu___4
let showable_fvar_binding : fvar_binding FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = fvb_to_string }
let check_valid_fvb (fvb : fvar_binding) : unit=
  if
    ((FStar_Pervasives_Native.uu___is_Some fvb.smt_token) ||
       (FStar_Pervasives_Native.uu___is_Some fvb.smt_fuel_partial_app))
      && fvb.fvb_thunked
  then
    (let uu___1 =
       let uu___2 = FStarC_Ident.string_of_lid fvb.fvar_lid in
       FStarC_Format.fmt1 "Unexpected thunked SMT symbol: %s" uu___2 in
     failwith uu___1)
  else
    if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
    then
      (let uu___2 =
         let uu___3 = FStarC_Ident.string_of_lid fvb.fvar_lid in
         FStarC_Format.fmt1 "Unexpected arity of thunked SMT symbol: %s"
           uu___3 in
       failwith uu___2)
    else ();
  (match fvb.smt_token with
   | FStar_Pervasives_Native.Some
       { FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.FreeV uu___1;
         FStarC_SMTEncoding_Term.freevars = uu___2;
         FStarC_SMTEncoding_Term.rng = uu___3;_}
       ->
       let uu___4 =
         let uu___5 = fvb_to_string fvb in
         FStarC_Format.fmt1 "bad fvb\n%s" uu___5 in
       failwith uu___4
   | uu___1 -> ())
let binder_of_eithervar (v : 'uuuuu) :
  ('uuuuu * 'uuuuu1 FStar_Pervasives_Native.option)=
  (v, FStar_Pervasives_Native.None)
type env_t =
  {
  bvar_bindings:
    (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term) FStarC_PIMap.t
      FStarC_PSMap.t
    ;
  fvar_bindings: (fvar_binding FStarC_PSMap.t * fvar_binding Prims.list) ;
  depth: Prims.int ;
  tcenv: FStarC_TypeChecker_Env.env ;
  warn: Prims.bool ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool ;
  global_cache:
    (FStarC_SMTEncoding_Term.decls_elt * FStarC_Ident.lident) FStarC_SMap.t }
let __proj__Mkenv_t__item__bvar_bindings (projectee : env_t) :
  (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term) FStarC_PIMap.t
    FStarC_PSMap.t=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> bvar_bindings
let __proj__Mkenv_t__item__fvar_bindings (projectee : env_t) :
  (fvar_binding FStarC_PSMap.t * fvar_binding Prims.list)=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> fvar_bindings
let __proj__Mkenv_t__item__depth (projectee : env_t) : Prims.int=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> depth
let __proj__Mkenv_t__item__tcenv (projectee : env_t) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> tcenv
let __proj__Mkenv_t__item__warn (projectee : env_t) : Prims.bool=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> warn
let __proj__Mkenv_t__item__nolabels (projectee : env_t) : Prims.bool=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> nolabels
let __proj__Mkenv_t__item__use_zfuel_name (projectee : env_t) : Prims.bool=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> use_zfuel_name
let __proj__Mkenv_t__item__encode_non_total_function_typ (projectee : env_t)
  : Prims.bool=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> encode_non_total_function_typ
let __proj__Mkenv_t__item__current_module_name (projectee : env_t) :
  Prims.string=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> current_module_name
let __proj__Mkenv_t__item__encoding_quantifier (projectee : env_t) :
  Prims.bool=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> encoding_quantifier
let __proj__Mkenv_t__item__global_cache (projectee : env_t) :
  (FStarC_SMTEncoding_Term.decls_elt * FStarC_Ident.lident) FStarC_SMap.t=
  match projectee with
  | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
      use_zfuel_name; encode_non_total_function_typ; current_module_name;
      encoding_quantifier; global_cache;_} -> global_cache
let print_env (e : env_t) : Prims.string=
  let bvars =
    FStarC_PSMap.fold e.bvar_bindings
      (fun _k pi acc ->
         FStarC_PIMap.fold pi
           (fun _i uu___ acc1 ->
              match uu___ with
              | (x, _term) ->
                  let uu___1 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
                  uu___1 :: acc1) acc) [] in
  let allvars =
    FStarC_PSMap.fold (FStar_Pervasives_Native.fst e.fvar_bindings)
      (fun _k fvb acc -> (fvb.fvar_lid) :: acc) [] in
  let last_fvar =
    match FStarC_List.rev allvars with
    | [] -> ""
    | l::uu___ ->
        let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident l in
        Prims.strcat "...," uu___1 in
  let uu___ =
    FStarC_Class_Show.show
      (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) allvars in
  let uu___1 =
    FStarC_Class_Show.show
      (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string) bvars in
  FStarC_Format.fmt2 "{allvars=%s; bvars=%s }" uu___ uu___1
let lookup_bvar_binding (env : env_t) (bv : FStarC_Syntax_Syntax.bv) :
  (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term)
    FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
    FStarC_PSMap.try_find env.bvar_bindings uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some bvs ->
      FStarC_PIMap.try_find bvs bv.FStarC_Syntax_Syntax.index
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let lookup_fvar_binding (env : env_t) (lid : FStarC_Ident.lident) :
  fvar_binding FStar_Pervasives_Native.option=
  let uu___ = FStarC_Ident.string_of_lid lid in
  FStarC_PSMap.try_find (FStar_Pervasives_Native.fst env.fvar_bindings) uu___
let add_bvar_binding (bvb : (FStarC_Syntax_Syntax.bv * 'uuuuu))
  (bvbs : (FStarC_Syntax_Syntax.bv * 'uuuuu) FStarC_PIMap.t FStarC_PSMap.t) :
  (FStarC_Syntax_Syntax.bv * 'uuuuu) FStarC_PIMap.t FStarC_PSMap.t=
  let uu___ =
    FStarC_Ident.string_of_id
      (FStar_Pervasives_Native.fst bvb).FStarC_Syntax_Syntax.ppname in
  FStarC_PSMap.modify bvbs uu___
    (fun pimap_opt ->
       let uu___1 =
         let uu___2 = FStarC_PIMap.empty () in
         FStarC_Option.dflt uu___2 pimap_opt in
       FStarC_PIMap.add uu___1
         (FStar_Pervasives_Native.fst bvb).FStarC_Syntax_Syntax.index bvb)
let add_fvar_binding (fvb : fvar_binding)
  (uu___ : (fvar_binding FStarC_PSMap.t * fvar_binding Prims.list)) :
  (fvar_binding FStarC_PSMap.t * fvar_binding Prims.list)=
  match uu___ with
  | (fvb_map, fvb_list) ->
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid fvb.fvar_lid in
        FStarC_PSMap.add fvb_map uu___2 fvb in
      (uu___1, (fvb :: fvb_list))
let fresh_fvar (mname : Prims.string) (x : Prims.string)
  (s : FStarC_SMTEncoding_Term.sort) :
  (Prims.string * FStarC_SMTEncoding_Term.term)=
  let xsym = varops.fresh mname x in
  let uu___ =
    let uu___1 = FStarC_SMTEncoding_Term.mk_fv (xsym, s) in
    FStarC_SMTEncoding_Util.mkFreeV uu___1 in
  (xsym, uu___)
let gen_term_var (env : env_t) (x : FStarC_Syntax_Syntax.bv) :
  (Prims.string * FStarC_SMTEncoding_Term.term * env_t)=
  let ysym =
    let uu___ =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int env.depth in
    Prims.strcat "@x" uu___ in
  let y =
    let uu___ =
      FStarC_SMTEncoding_Term.mk_fv (ysym, FStarC_SMTEncoding_Term.Term_sort) in
    FStarC_SMTEncoding_Util.mkFreeV uu___ in
  let uu___ =
    let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
    let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
    {
      bvar_bindings = uu___1;
      fvar_bindings = (env.fvar_bindings);
      depth = (env.depth + Prims.int_one);
      tcenv = uu___2;
      warn = (env.warn);
      nolabels = (env.nolabels);
      use_zfuel_name = (env.use_zfuel_name);
      encode_non_total_function_typ = (env.encode_non_total_function_typ);
      current_module_name = (env.current_module_name);
      encoding_quantifier = (env.encoding_quantifier);
      global_cache = (env.global_cache)
    } in
  (ysym, y, uu___)
let new_term_constant (env : env_t) (x : FStarC_Syntax_Syntax.bv) :
  (Prims.string * FStarC_SMTEncoding_Term.term * env_t)=
  let ysym =
    varops.new_var x.FStarC_Syntax_Syntax.ppname x.FStarC_Syntax_Syntax.index in
  let y = FStarC_SMTEncoding_Util.mkApp (ysym, []) in
  let uu___ =
    let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
    let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
    {
      bvar_bindings = uu___1;
      fvar_bindings = (env.fvar_bindings);
      depth = (env.depth);
      tcenv = uu___2;
      warn = (env.warn);
      nolabels = (env.nolabels);
      use_zfuel_name = (env.use_zfuel_name);
      encode_non_total_function_typ = (env.encode_non_total_function_typ);
      current_module_name = (env.current_module_name);
      encoding_quantifier = (env.encoding_quantifier);
      global_cache = (env.global_cache)
    } in
  (ysym, y, uu___)
let new_term_constant_from_string (env : env_t) (x : FStarC_Syntax_Syntax.bv)
  (str : Prims.string) :
  (Prims.string * FStarC_SMTEncoding_Term.term * env_t)=
  let ysym = varops.mk_unique str in
  let y = FStarC_SMTEncoding_Util.mkApp (ysym, []) in
  let uu___ =
    let uu___1 = add_bvar_binding (x, y) env.bvar_bindings in
    let uu___2 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
    {
      bvar_bindings = uu___1;
      fvar_bindings = (env.fvar_bindings);
      depth = (env.depth);
      tcenv = uu___2;
      warn = (env.warn);
      nolabels = (env.nolabels);
      use_zfuel_name = (env.use_zfuel_name);
      encode_non_total_function_typ = (env.encode_non_total_function_typ);
      current_module_name = (env.current_module_name);
      encoding_quantifier = (env.encoding_quantifier);
      global_cache = (env.global_cache)
    } in
  (ysym, y, uu___)
let push_term_var (env : env_t) (x : FStarC_Syntax_Syntax.bv)
  (t : FStarC_SMTEncoding_Term.term) : env_t=
  let uu___ = add_bvar_binding (x, t) env.bvar_bindings in
  let uu___1 = FStarC_TypeChecker_Env.push_bv env.tcenv x in
  {
    bvar_bindings = uu___;
    fvar_bindings = (env.fvar_bindings);
    depth = (env.depth);
    tcenv = uu___1;
    warn = (env.warn);
    nolabels = (env.nolabels);
    use_zfuel_name = (env.use_zfuel_name);
    encode_non_total_function_typ = (env.encode_non_total_function_typ);
    current_module_name = (env.current_module_name);
    encoding_quantifier = (env.encoding_quantifier);
    global_cache = (env.global_cache)
  }
let lookup_term_var (env : env_t) (a : FStarC_Syntax_Syntax.bv) :
  FStarC_SMTEncoding_Term.term=
  let uu___ = lookup_bvar_binding env a in
  match uu___ with
  | FStar_Pervasives_Native.Some (b, t) -> t
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv a in
        let uu___3 = print_env env in
        FStarC_Format.fmt2
          "Bound term variable not found  %s in environment: %s" uu___2
          uu___3 in
      failwith uu___1
let mk_fvb (lid : FStarC_Ident.lident) (fname : Prims.string)
  (arity : Prims.int) (univ_arity : Prims.int)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  (fuel_partial_app :
    (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term)
      FStar_Pervasives_Native.option)
  (thunked : Prims.bool)
  (univs : FStarC_Syntax_Syntax.univ_names FStar_Pervasives_Native.option) :
  fvar_binding=
  let fvb =
    {
      fvar_lid = lid;
      univ_arity;
      smt_arity = arity;
      smt_id = fname;
      smt_token = ftok;
      smt_fuel_partial_app = fuel_partial_app;
      fvb_thunked = thunked;
      needs_fuel_and_universe_instantiations = univs
    } in
  check_valid_fvb fvb; fvb
let new_term_constant_and_tok_from_lid_aux (env : env_t)
  (x : FStarC_Ident.lident) (arity : Prims.int) (univ_arity : Prims.int)
  (thunked : Prims.bool) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t)=
  let fname = varops.new_fvar x in
  let uu___ =
    if thunked
    then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
    else
      (let ftok_name = Prims.strcat fname "@tok" in
       let ftok = FStarC_SMTEncoding_Util.mkApp (ftok_name, []) in
       ((FStar_Pervasives_Native.Some ftok_name),
         (FStar_Pervasives_Native.Some ftok))) in
  match uu___ with
  | (ftok_name, ftok) ->
      let fvb =
        mk_fvb x fname arity univ_arity ftok FStar_Pervasives_Native.None
          thunked FStar_Pervasives_Native.None in
      let uu___1 =
        let uu___2 = add_fvar_binding fvb env.fvar_bindings in
        {
          bvar_bindings = (env.bvar_bindings);
          fvar_bindings = uu___2;
          depth = (env.depth);
          tcenv = (env.tcenv);
          warn = (env.warn);
          nolabels = (env.nolabels);
          use_zfuel_name = (env.use_zfuel_name);
          encode_non_total_function_typ = (env.encode_non_total_function_typ);
          current_module_name = (env.current_module_name);
          encoding_quantifier = (env.encoding_quantifier);
          global_cache = (env.global_cache)
        } in
      (fname, ftok_name, uu___1)
let new_term_constant_and_tok_from_lid (env : env_t)
  (x : FStarC_Ident.lident) (arity : Prims.int) (univ_arity : Prims.int) :
  (Prims.string * Prims.string * env_t)=
  let uu___ =
    new_term_constant_and_tok_from_lid_aux env x arity univ_arity false in
  match uu___ with
  | (fname, ftok_name_opt, env1) ->
      (fname, (FStar_Pervasives_Native.__proj__Some__item__v ftok_name_opt),
        env1)
let new_term_constant_and_tok_from_lid_maybe_thunked (env : env_t)
  (x : FStarC_Ident.lident) (arity : Prims.int) (th : Prims.int) :
  Prims.bool ->
    (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t)=
  new_term_constant_and_tok_from_lid_aux env x arity th
let fail_fvar_lookup (env : env_t) (a : FStarC_Ident.lident) : 'uuuuu=
  let q = FStarC_TypeChecker_Env.lookup_qname env.tcenv a in
  match q with
  | FStar_Pervasives_Native.None ->
      let uu___ =
        let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident a in
        FStarC_Format.fmt1
          "Name %s not found in the smtencoding and typechecker env" uu___1 in
      failwith uu___
  | uu___ ->
      let quals = FStarC_TypeChecker_Env.quals_of_qninfo q in
      if
        (FStar_Pervasives_Native.uu___is_Some quals) &&
          (FStarC_List.contains
             FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen
             (FStar_Pervasives_Native.__proj__Some__item__v quals))
      then
        let uu___1 =
          let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident a in
          FStarC_Format.fmt1
            "Name %s not found in the smtencoding env (the symbol is marked unfold, expected it to reduce)"
            uu___2 in
        FStarC_Errors.raise_error FStarC_Ident.hasrange_lident a
          FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___1)
      else
        (let uu___2 =
           let uu___3 = FStarC_Class_Show.show FStarC_Ident.showable_lident a in
           FStarC_Format.fmt1 "Name %s not found in the smtencoding env"
             uu___3 in
         failwith uu___2)
let lookup_lid (env : env_t) (a : FStarC_Ident.lident) : fvar_binding=
  let uu___ = lookup_fvar_binding env a in
  match uu___ with
  | FStar_Pervasives_Native.None -> fail_fvar_lookup env a
  | FStar_Pervasives_Native.Some s -> (check_valid_fvb s; s)
let push_free_var_maybe_thunked_with_univs (env : env_t)
  (x : FStarC_Ident.lident) (arity : Prims.int) (univ_arity : Prims.int)
  (fname : Prims.string)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  (thunked : Prims.bool)
  (univs : FStarC_Syntax_Syntax.univ_names FStar_Pervasives_Native.option) :
  env_t=
  let fvb =
    mk_fvb x fname arity univ_arity ftok FStar_Pervasives_Native.None thunked
      univs in
  let uu___ = add_fvar_binding fvb env.fvar_bindings in
  {
    bvar_bindings = (env.bvar_bindings);
    fvar_bindings = uu___;
    depth = (env.depth);
    tcenv = (env.tcenv);
    warn = (env.warn);
    nolabels = (env.nolabels);
    use_zfuel_name = (env.use_zfuel_name);
    encode_non_total_function_typ = (env.encode_non_total_function_typ);
    current_module_name = (env.current_module_name);
    encoding_quantifier = (env.encoding_quantifier);
    global_cache = (env.global_cache)
  }
let push_free_var_maybe_thunked (env : env_t) (x : FStarC_Ident.lident)
  (arity : Prims.int) (univ_arity : Prims.int) (fname : Prims.string)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  (fthunked : Prims.bool) : env_t=
  push_free_var_maybe_thunked_with_univs env x arity univ_arity fname ftok
    fthunked FStar_Pervasives_Native.None
let push_free_var_tok_with_fuel_and_univs (env : env_t)
  (x : FStarC_Ident.lident) (arity : Prims.int) (univ_arity : Prims.int)
  (fname : Prims.string)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  (univs : FStarC_Syntax_Syntax.univ_names) : env_t=
  push_free_var_maybe_thunked_with_univs env x arity univ_arity fname ftok
    false (FStar_Pervasives_Native.Some univs)
let push_free_var (env : env_t) (x : FStarC_Ident.lident) (arity : Prims.int)
  (univ_arity : Prims.int) (fname : Prims.string)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option) :
  env_t= push_free_var_maybe_thunked env x arity univ_arity fname ftok false
let push_free_var_thunk (env : env_t) (x : FStarC_Ident.lident)
  (arity : Prims.int) (univ_arity : Prims.int) (fname : Prims.string)
  (ftok : FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option) :
  env_t=
  push_free_var_maybe_thunked env x arity univ_arity fname ftok
    (arity = Prims.int_zero)
let push_zfuel_name (env : env_t) (x : FStarC_Ident.lident)
  (f : Prims.string) (ftok : Prims.string) : env_t=
  let fvb = lookup_lid env x in
  let t3 =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_SMTEncoding_Util.mkApp ("ZFuel", []) in [uu___2] in
      (f, uu___1) in
    FStarC_SMTEncoding_Util.mkApp uu___ in
  let t3' =
    let uu___ = FStarC_SMTEncoding_Util.mkApp (ftok, []) in
    let uu___1 = FStarC_SMTEncoding_Util.mkApp ("ZFuel", []) in
    FStarC_SMTEncoding_Term.mk_ApplyTF uu___ uu___1 in
  let fvb1 =
    mk_fvb x fvb.smt_id fvb.smt_arity fvb.univ_arity fvb.smt_token
      (FStar_Pervasives_Native.Some (t3, t3')) false
      FStar_Pervasives_Native.None in
  let uu___ = add_fvar_binding fvb1 env.fvar_bindings in
  {
    bvar_bindings = (env.bvar_bindings);
    fvar_bindings = uu___;
    depth = (env.depth);
    tcenv = (env.tcenv);
    warn = (env.warn);
    nolabels = (env.nolabels);
    use_zfuel_name = (env.use_zfuel_name);
    encode_non_total_function_typ = (env.encode_non_total_function_typ);
    current_module_name = (env.current_module_name);
    encoding_quantifier = (env.encoding_quantifier);
    global_cache = (env.global_cache)
  }
let force_thunk (fvb : fvar_binding) : FStarC_SMTEncoding_Term.term=
  if (Prims.op_Negation fvb.fvb_thunked) || (fvb.smt_arity <> Prims.int_zero)
  then
    (let uu___1 =
       let uu___2 = FStarC_Ident.string_of_lid fvb.fvar_lid in
       FStarC_Format.fmt1 "Forcing a non-thunk %s in the SMT encoding" uu___2 in
     failwith uu___1)
  else ();
  FStarC_SMTEncoding_Util.mkFreeV
    (FStarC_SMTEncoding_Term.FV
       ((fvb.smt_id), FStarC_SMTEncoding_Term.Term_sort, true))
let try_lookup_free_var (env : env_t) (l : FStarC_Ident.lident) :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option=
  let uu___ = lookup_fvar_binding env l in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some fvb ->
      ((let uu___2 = FStarC_Effect.op_Bang dbg_PartialApp in
        if uu___2
        then
          let uu___3 = FStarC_Ident.string_of_lid l in
          let uu___4 = fvb_to_string fvb in
          FStarC_Format.print2 "Looked up %s found\n%s\n" uu___3 uu___4
        else ());
       if fvb.fvb_thunked
       then
         (let uu___2 = force_thunk fvb in FStar_Pervasives_Native.Some uu___2)
       else
         (match fvb.smt_fuel_partial_app with
          | FStar_Pervasives_Native.Some (uu___3, f) when env.use_zfuel_name
              -> FStar_Pervasives_Native.Some f
          | uu___3 ->
              (match fvb.smt_token with
               | FStar_Pervasives_Native.Some t ->
                   (match t.FStarC_SMTEncoding_Term.tm with
                    | FStarC_SMTEncoding_Term.App (uu___4, fuel::[]) ->
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStarC_SMTEncoding_Term.fv_of_term fuel in
                            FStarC_SMTEncoding_Term.fv_name uu___7 in
                          FStarC_Util.starts_with uu___6 "fuel" in
                        if uu___5
                        then
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                FStarC_SMTEncoding_Term.mk_fv
                                  ((fvb.smt_id),
                                    FStarC_SMTEncoding_Term.Term_sort) in
                              FStarC_SMTEncoding_Util.mkFreeV uu___8 in
                            FStarC_SMTEncoding_Term.mk_ApplyTF uu___7 fuel in
                          FStar_Pervasives_Native.Some uu___6
                        else FStar_Pervasives_Native.Some t
                    | uu___4 -> FStar_Pervasives_Native.Some t)
               | uu___4 -> FStar_Pervasives_Native.None)))
let lookup_free_var (env : env_t) (a : FStarC_Ident.lident) :
  FStarC_SMTEncoding_Term.term=
  let uu___ = try_lookup_free_var env a in
  match uu___ with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None -> fail_fvar_lookup env a
let lookup_free_var_name (env : env_t) (a : FStarC_Ident.lident) :
  fvar_binding= lookup_lid env a
let lookup_free_var_sym (env : env_t) (a : FStarC_Ident.lident) :
  ((FStarC_SMTEncoding_Term.op, FStarC_SMTEncoding_Term.term)
    FStar_Pervasives.either * FStarC_SMTEncoding_Term.term Prims.list *
    Prims.int)=
  let fvb = lookup_lid env a in
  match fvb.smt_fuel_partial_app with
  | FStar_Pervasives_Native.Some
      ({ FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App (g, zf);
         FStarC_SMTEncoding_Term.freevars = uu___;
         FStarC_SMTEncoding_Term.rng = uu___1;_},
       uu___2)
      when env.use_zfuel_name ->
      ((FStar_Pervasives.Inl g), zf, (fvb.smt_arity + Prims.int_one))
  | uu___ ->
      (match fvb.smt_token with
       | FStar_Pervasives_Native.None when fvb.fvb_thunked ->
           let uu___1 =
             let uu___2 = force_thunk fvb in FStar_Pervasives.Inr uu___2 in
           (uu___1, [], (fvb.smt_arity))
       | FStar_Pervasives_Native.None ->
           ((FStar_Pervasives.Inl (FStarC_SMTEncoding_Term.Var (fvb.smt_id))),
             [], (fvb.smt_arity))
       | FStar_Pervasives_Native.Some sym ->
           (match sym.FStarC_SMTEncoding_Term.tm with
            | FStarC_SMTEncoding_Term.App (g, fuel::[]) ->
                ((FStar_Pervasives.Inl g), [fuel],
                  (fvb.smt_arity + Prims.int_one))
            | uu___1 ->
                ((FStar_Pervasives.Inl
                    (FStarC_SMTEncoding_Term.Var (fvb.smt_id))), [],
                  (fvb.smt_arity))))
let tok_of_name (env : env_t) (nm : Prims.string) :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_PSMap.find_map (FStar_Pervasives_Native.fst env.fvar_bindings)
      (fun uu___1 fvb ->
         check_valid_fvb fvb;
         if fvb.smt_id = nm
         then fvb.smt_token
         else FStar_Pervasives_Native.None) in
  match uu___ with
  | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
  | FStar_Pervasives_Native.None ->
      FStarC_PSMap.find_map env.bvar_bindings
        (fun uu___1 pi ->
           FStarC_PIMap.fold pi
             (fun uu___2 y res ->
                match (res, y) with
                | (FStar_Pervasives_Native.Some uu___3, uu___4) -> res
                | (FStar_Pervasives_Native.None,
                   (uu___3,
                    {
                      FStarC_SMTEncoding_Term.tm =
                        FStarC_SMTEncoding_Term.App
                        (FStarC_SMTEncoding_Term.Var sym, []);
                      FStarC_SMTEncoding_Term.freevars = uu___4;
                      FStarC_SMTEncoding_Term.rng = uu___5;_}))
                    when sym = nm ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.snd y)
                | uu___3 -> FStar_Pervasives_Native.None)
             FStar_Pervasives_Native.None)
let reset_current_module_fvbs (env : env_t) : env_t=
  {
    bvar_bindings = (env.bvar_bindings);
    fvar_bindings = ((FStar_Pervasives_Native.fst env.fvar_bindings), []);
    depth = (env.depth);
    tcenv = (env.tcenv);
    warn = (env.warn);
    nolabels = (env.nolabels);
    use_zfuel_name = (env.use_zfuel_name);
    encode_non_total_function_typ = (env.encode_non_total_function_typ);
    current_module_name = (env.current_module_name);
    encoding_quantifier = (env.encoding_quantifier);
    global_cache = (env.global_cache)
  }
let get_current_module_fvbs (env : env_t) : fvar_binding Prims.list=
  FStar_Pervasives_Native.snd env.fvar_bindings
let add_fvar_binding_to_env (fvb : fvar_binding) (env : env_t) : env_t=
  let uu___ = add_fvar_binding fvb env.fvar_bindings in
  {
    bvar_bindings = (env.bvar_bindings);
    fvar_bindings = uu___;
    depth = (env.depth);
    tcenv = (env.tcenv);
    warn = (env.warn);
    nolabels = (env.nolabels);
    use_zfuel_name = (env.use_zfuel_name);
    encode_non_total_function_typ = (env.encode_non_total_function_typ);
    current_module_name = (env.current_module_name);
    encoding_quantifier = (env.encoding_quantifier);
    global_cache = (env.global_cache)
  }
