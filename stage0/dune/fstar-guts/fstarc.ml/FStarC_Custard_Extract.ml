open Prims
type spec_key =
  {
  sk_lid: FStarC_Ident.lident ;
  sk_args: (Prims.int * FStarC_Syntax_Syntax.term) Prims.list ;
  sk_subst: (Prims.int * FStarC_Syntax_Syntax.term) Prims.list ;
  sk_holes: Prims.int }
let __proj__Mkspec_key__item__sk_lid (projectee : spec_key) :
  FStarC_Ident.lident=
  match projectee with | { sk_lid; sk_args; sk_subst; sk_holes;_} -> sk_lid
let __proj__Mkspec_key__item__sk_args (projectee : spec_key) :
  (Prims.int * FStarC_Syntax_Syntax.term) Prims.list=
  match projectee with | { sk_lid; sk_args; sk_subst; sk_holes;_} -> sk_args
let __proj__Mkspec_key__item__sk_subst (projectee : spec_key) :
  (Prims.int * FStarC_Syntax_Syntax.term) Prims.list=
  match projectee with | { sk_lid; sk_args; sk_subst; sk_holes;_} -> sk_subst
let __proj__Mkspec_key__item__sk_holes (projectee : spec_key) : Prims.int=
  match projectee with | { sk_lid; sk_args; sk_subst; sk_holes;_} -> sk_holes
let no_specialize_lid : FStarC_Ident.lident=
  FStarC_Parser_Const.p2l ["FStar"; "Custard"; "no_specialize"]
let norm_steps_base : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.DontUnfoldAttr [no_specialize_lid];
  FStarC_TypeChecker_Env.Weak;
  FStarC_TypeChecker_Env.AllowUnboundUniverses;
  FStarC_TypeChecker_Env.EraseUniverses;
  FStarC_TypeChecker_Env.Beta;
  FStarC_TypeChecker_Env.Iota;
  FStarC_TypeChecker_Env.Unascribe;
  FStarC_TypeChecker_Env.Unmeta;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant]
let key_norm_steps : FStarC_TypeChecker_Env.step Prims.list=
  FStarC_TypeChecker_Env.Primops :: norm_steps_base
let subst_norm_steps : FStarC_TypeChecker_Env.step Prims.list=
  FStarC_TypeChecker_Env.SafePrimops :: FStarC_TypeChecker_Env.Weak ::
  FStarC_TypeChecker_Env.HNF :: norm_steps_base
let key_of_const (c : FStarC_Const.sconst) : Prims.string=
  match c with
  | FStarC_Const.Const_effect -> "Effect"
  | FStarC_Const.Const_unit -> "()"
  | FStarC_Const.Const_bool b -> if b then "true" else "false"
  | FStarC_Const.Const_real r -> Prims.strcat (FStarC_Real.to_string r) "R"
  | FStarC_Const.Const_char c1 ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            (FStarC_Util.int_of_char c1) in
        Prims.strcat uu___1 "'" in
      Prims.strcat "'" uu___
  | FStarC_Const.Const_string (s, uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Custard_Syntax.escape_string s in
        Prims.strcat uu___2 "\"" in
      Prims.strcat "\"" uu___1
  | FStarC_Const.Const_int (v, uu___) ->
      FStarC_Class_Show.show FStarC_Class_Show.showable_int v
  | FStarC_Const.Const_machine_int (v, uu___, sg, w) ->
      let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int v in
      Prims.strcat uu___1
        (Prims.strcat
           (match sg with
            | FStarC_Const.Unsigned -> "u"
            | FStarC_Const.Signed -> "s")
           (match w with
            | FStarC_Const.Int8 -> "8"
            | FStarC_Const.Int16 -> "16"
            | FStarC_Const.Int32 -> "32"
            | FStarC_Const.Int64 -> "64"
            | FStarC_Const.Sizet -> "sz"))
  | FStarC_Const.Const_range uu___ -> "<range>"
  | FStarC_Const.Const_range_of -> "range_of"
  | FStarC_Const.Const_set_range_of -> "set_range_of"
  | FStarC_Const.Const_reify lopt ->
      Prims.strcat "reify"
        (match lopt with
         | FStar_Pervasives_Native.None -> ""
         | FStar_Pervasives_Native.Some l ->
             Prims.strcat "<"
               (Prims.strcat (FStarC_Ident.string_of_lid l) ">"))
  | FStarC_Const.Const_reflect l ->
      Prims.strcat "reflect<"
        (Prims.strcat (FStarC_Ident.string_of_lid l) ">")
let rec key_into (acc : Prims.string Prims.list FStarC_Effect.ref)
  (t : FStarC_Syntax_Syntax.term) : unit=
  let emit s =
    let uu___ = let uu___1 = FStarC_Effect.op_Bang acc in s :: uu___1 in
    FStarC_Effect.op_Colon_Equals acc uu___ in
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_bvar bv ->
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            bv.FStarC_Syntax_Syntax.index in
        Prims.strcat "@" uu___2 in
      emit uu___1
  | FStarC_Syntax_Syntax.Tm_name bv ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int
                bv.FStarC_Syntax_Syntax.index in
            Prims.strcat "#" uu___4 in
          Prims.strcat
            (FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname) uu___3 in
        Prims.strcat "%" uu___2 in
      emit uu___1
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      emit (FStarC_Ident.string_of_lid (FStarC_Syntax_Syntax.lid_of_fv fv))
  | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> key_into acc t1
  | FStarC_Syntax_Syntax.Tm_constant c ->
      let uu___1 = key_of_const c in emit uu___1
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> emit "Type"
  | FStarC_Syntax_Syntax.Tm_abs
      { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.body = body;
        FStarC_Syntax_Syntax.rc_opt = uu___1;_}
      ->
      (emit "(fun ";
       key_of_binder acc b;
       emit " -> ";
       key_into acc body;
       emit ")")
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.b1 = b; FStarC_Syntax_Syntax.comp = comp;_} ->
      (emit "(";
       key_of_binder acc b;
       emit " -> ";
       key_of_comp acc comp;
       emit ")")
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = b; FStarC_Syntax_Syntax.phi = phi;_} ->
      (emit "({";
       key_into acc b.FStarC_Syntax_Syntax.sort;
       emit "|";
       key_into acc phi;
       emit "})")
  | FStarC_Syntax_Syntax.Tm_app
      { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.arg = arg;_} ->
      (emit "("; key_into acc hd; emit " "; key_of_arg acc arg; emit ")")
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = scrutinee;
        FStarC_Syntax_Syntax.ret_opt = uu___1;
        FStarC_Syntax_Syntax.brs = brs;
        FStarC_Syntax_Syntax.rc_opt1 = uu___2;_}
      ->
      (emit "(match ";
       key_into acc scrutinee;
       emit " with";
       FStarC_List.iter (key_of_branch acc) brs;
       emit ")")
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = tm; FStarC_Syntax_Syntax.asc = uu___1;
        FStarC_Syntax_Syntax.eff_opt = uu___2;_}
      -> key_into acc tm
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = tm; FStarC_Syntax_Syntax.meta = uu___1;_}
      -> key_into acc tm
  | FStarC_Syntax_Syntax.Tm_let
      { FStarC_Syntax_Syntax.lbs = (r, lbs);
        FStarC_Syntax_Syntax.body1 = body;_}
      ->
      (emit (Prims.strcat "(let" (if r then " rec" else ""));
       FStarC_List.iteri
         (fun i lb ->
            if i > Prims.int_zero then emit " and " else (); key_of_lb acc lb)
         lbs;
       emit " in ";
       key_into acc body;
       emit ")")
  | FStarC_Syntax_Syntax.Tm_uvar (u, uu___1) ->
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Syntax_Unionfind.uvar_id
              u.FStarC_Syntax_Syntax.ctx_uvar_head in
          FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___4 in
        Prims.strcat "?" uu___3 in
      emit uu___2
  | FStarC_Syntax_Syntax.Tm_quoted (t1, uu___1) ->
      (emit "(quote "; key_into acc t1; emit ")")
  | FStarC_Syntax_Syntax.Tm_lazy uu___1 ->
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Syntax_Util.unlazy t in
          FStarC_Syntax_Subst.compress uu___4 in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_lazy uu___3 -> emit "<lazy>"
       | uu___3 ->
           let uu___4 = FStarC_Syntax_Util.unlazy t in key_into acc uu___4)
  | FStarC_Syntax_Syntax.Tm_unknown -> emit "_"
  | FStarC_Syntax_Syntax.Tm_delayed uu___1 -> emit "<delayed>"
and key_of_binder (acc : Prims.string Prims.list FStarC_Effect.ref)
  (b : FStarC_Syntax_Syntax.binder) : unit=
  key_into acc (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
and key_of_arg (acc : Prims.string Prims.list FStarC_Effect.ref)
  (a : FStarC_Syntax_Syntax.arg) : unit=
  key_into acc (FStar_Pervasives_Native.fst a)
and key_of_comp (acc : Prims.string Prims.list FStarC_Effect.ref)
  (c : FStarC_Syntax_Syntax.comp) : unit=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Comp ct ->
      ((let uu___1 =
          let uu___2 = FStarC_Effect.op_Bang acc in
          (Prims.strcat
             (FStarC_Ident.string_of_lid ct.FStarC_Syntax_Syntax.effect_name)
             " ")
            :: uu___2 in
        FStarC_Effect.op_Colon_Equals acc uu___1);
       key_into acc ct.FStarC_Syntax_Syntax.result_typ)
and key_of_branch (acc : Prims.string Prims.list FStarC_Effect.ref)
  (br : FStarC_Syntax_Syntax.branch) : unit=
  let uu___ = br in
  match uu___ with
  | (p, w, e) ->
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang acc in " | " :: uu___3 in
        FStarC_Effect.op_Colon_Equals acc uu___2);
       key_of_pat acc p;
       (match w with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some w1 ->
            ((let uu___5 =
                let uu___6 = FStarC_Effect.op_Bang acc in " when " :: uu___6 in
              FStarC_Effect.op_Colon_Equals acc uu___5);
             key_into acc w1));
       (let uu___5 =
          let uu___6 = FStarC_Effect.op_Bang acc in " -> " :: uu___6 in
        FStarC_Effect.op_Colon_Equals acc uu___5);
       key_into acc e)
and key_of_pat (acc : Prims.string Prims.list FStarC_Effect.ref)
  (p : FStarC_Syntax_Syntax.pat) : unit=
  match p.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_constant c ->
      let uu___ =
        let uu___1 = key_of_const c in
        let uu___2 = FStarC_Effect.op_Bang acc in uu___1 :: uu___2 in
      FStarC_Effect.op_Colon_Equals acc uu___
  | FStarC_Syntax_Syntax.Pat_var uu___ ->
      let uu___1 = let uu___2 = FStarC_Effect.op_Bang acc in "_" :: uu___2 in
      FStarC_Effect.op_Colon_Equals acc uu___1
  | FStarC_Syntax_Syntax.Pat_dot_term uu___ ->
      let uu___1 = let uu___2 = FStarC_Effect.op_Bang acc in "." :: uu___2 in
      FStarC_Effect.op_Colon_Equals acc uu___1
  | FStarC_Syntax_Syntax.Pat_cons (fv, uu___, ps) ->
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang acc in
          (Prims.strcat "("
             (FStarC_Ident.string_of_lid (FStarC_Syntax_Syntax.lid_of_fv fv)))
            :: uu___3 in
        FStarC_Effect.op_Colon_Equals acc uu___2);
       FStarC_List.iter
         (fun uu___3 ->
            match uu___3 with
            | (p1, uu___4) ->
                ((let uu___6 =
                    let uu___7 = FStarC_Effect.op_Bang acc in " " :: uu___7 in
                  FStarC_Effect.op_Colon_Equals acc uu___6);
                 key_of_pat acc p1)) ps;
       (let uu___3 = let uu___4 = FStarC_Effect.op_Bang acc in ")" :: uu___4 in
        FStarC_Effect.op_Colon_Equals acc uu___3))
and key_of_lb (acc : Prims.string Prims.list FStarC_Effect.ref)
  (lb : FStarC_Syntax_Syntax.letbinding) : unit=
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang acc in
     (match lb.FStarC_Syntax_Syntax.lbname with
      | FStar_Pervasives.Inl uu___3 -> "@"
      | FStar_Pervasives.Inr fv ->
          FStarC_Ident.string_of_lid (FStarC_Syntax_Syntax.lid_of_fv fv))
       :: uu___2 in
   FStarC_Effect.op_Colon_Equals acc uu___1);
  (let uu___2 = let uu___3 = FStarC_Effect.op_Bang acc in " : " :: uu___3 in
   FStarC_Effect.op_Colon_Equals acc uu___2);
  key_into acc lb.FStarC_Syntax_Syntax.lbtyp;
  (let uu___4 = let uu___5 = FStarC_Effect.op_Bang acc in " = " :: uu___5 in
   FStarC_Effect.op_Colon_Equals acc uu___4);
  key_into acc lb.FStarC_Syntax_Syntax.lbdef
let key_of_term (t : FStarC_Syntax_Syntax.term) : Prims.string=
  let acc = FStarC_Effect.mk_ref [] in
  key_into acc t;
  (let uu___1 =
     let uu___2 = FStarC_Effect.op_Bang acc in FStarC_List.rev uu___2 in
   FStarC_String.concat "" uu___1)
let string_of_key (k : spec_key) : Prims.string=
  FStarC_Custard_Prof.timed "key"
    (fun uu___ ->
       let acc = FStarC_Effect.mk_ref [] in
       (let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang acc in
          (FStarC_Ident.string_of_lid k.sk_lid) :: uu___3 in
        FStarC_Effect.op_Colon_Equals acc uu___2);
       if k.sk_holes <> Prims.int_zero
       then
         (let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int
                  k.sk_holes in
              Prims.strcat "/" uu___5 in
            let uu___5 = FStarC_Effect.op_Bang acc in uu___4 :: uu___5 in
          FStarC_Effect.op_Colon_Equals acc uu___3)
       else ();
       FStarC_List.iter
         (fun uu___4 ->
            match uu___4 with
            | (i, t) ->
                ((let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_int i in
                        Prims.strcat uu___9 "=" in
                      Prims.strcat "#" uu___8 in
                    let uu___8 = FStarC_Effect.op_Bang acc in uu___7 ::
                      uu___8 in
                  FStarC_Effect.op_Colon_Equals acc uu___6);
                 key_into acc t)) k.sk_args;
       (let uu___4 =
          let uu___5 = FStarC_Effect.op_Bang acc in FStarC_List.rev uu___5 in
        FStarC_String.concat "" uu___4))
type state =
  {
  deps: FStarC_Parser_Dep.deps ;
  env: FStarC_TypeChecker_Env.env FStarC_Effect.ref ;
  names: FStarC_Custard_Syntax.name FStarC_SMap.t ;
  emitted: FStarC_Custard_Syntax.decl FStarC_SMap.t ;
  order: Prims.string Prims.list FStarC_Effect.ref ;
  classes: FStarC_Custard_Mono.bclass Prims.list FStarC_SMap.t ;
  bflags: Prims.bool Prims.list FStarC_SMap.t ;
  counts: Prims.int FStarC_SMap.t ;
  suffixes: Prims.bool FStarC_SMap.t ;
  fuel: Prims.int FStarC_Effect.ref ;
  chain: Prims.string Prims.list FStarC_Effect.ref ;
  lifted:
    (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.cty Prims.list *
      FStarC_Custard_Syntax.binder Prims.list * FStarC_Custard_Syntax.cty *
      FStarC_Syntax_Syntax.bv Prims.list) FStarC_SMap.t
    ;
  cur: FStarC_Custard_Syntax.name FStarC_Effect.ref ;
  cur_lid:
    FStarC_Ident.lident FStar_Pervasives_Native.option FStarC_Effect.ref ;
  chainlids: FStarC_Ident.lident Prims.list FStarC_Effect.ref ;
  letdefs: FStarC_Syntax_Syntax.term FStarC_SMap.t ;
  effletdefs: unit FStarC_SMap.t ;
  defbinders: unit FStarC_SMap.t ;
  lettys: FStarC_Custard_Syntax.cty FStarC_SMap.t ;
  abbrevs:
    (Prims.string Prims.list * FStarC_Custard_Syntax.cty) FStarC_SMap.t ;
  links: FStarC_Custard_Unit.links ;
  imports:
    (FStarC_Custard_Syntax.decl * FStarC_Custard_Syntax.type_info
      FStar_Pervasives_Native.option) Prims.list FStarC_Effect.ref
    ;
  roots: Prims.bool FStarC_SMap.t ;
  nfe: FStarC_Syntax_Syntax.sigelt FStarC_SMap.t }
let __proj__Mkstate__item__deps (projectee : state) : FStarC_Parser_Dep.deps=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> deps
let __proj__Mkstate__item__env (projectee : state) :
  FStarC_TypeChecker_Env.env FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> env
let __proj__Mkstate__item__names (projectee : state) :
  FStarC_Custard_Syntax.name FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> names
let __proj__Mkstate__item__emitted (projectee : state) :
  FStarC_Custard_Syntax.decl FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> emitted
let __proj__Mkstate__item__order (projectee : state) :
  Prims.string Prims.list FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> order
let __proj__Mkstate__item__classes (projectee : state) :
  FStarC_Custard_Mono.bclass Prims.list FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> classes
let __proj__Mkstate__item__bflags (projectee : state) :
  Prims.bool Prims.list FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> bflags
let __proj__Mkstate__item__counts (projectee : state) :
  Prims.int FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> counts
let __proj__Mkstate__item__suffixes (projectee : state) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> suffixes
let __proj__Mkstate__item__fuel (projectee : state) :
  Prims.int FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> fuel
let __proj__Mkstate__item__chain (projectee : state) :
  Prims.string Prims.list FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> chain
let __proj__Mkstate__item__lifted (projectee : state) :
  (FStarC_Custard_Syntax.name * FStarC_Custard_Syntax.cty Prims.list *
    FStarC_Custard_Syntax.binder Prims.list * FStarC_Custard_Syntax.cty *
    FStarC_Syntax_Syntax.bv Prims.list) FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> lifted
let __proj__Mkstate__item__cur (projectee : state) :
  FStarC_Custard_Syntax.name FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> cur
let __proj__Mkstate__item__cur_lid (projectee : state) :
  FStarC_Ident.lident FStar_Pervasives_Native.option FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> cur_lid
let __proj__Mkstate__item__chainlids (projectee : state) :
  FStarC_Ident.lident Prims.list FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> chainlids
let __proj__Mkstate__item__letdefs (projectee : state) :
  FStarC_Syntax_Syntax.term FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> letdefs
let __proj__Mkstate__item__effletdefs (projectee : state) :
  unit FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} ->
      effletdefs
let __proj__Mkstate__item__defbinders (projectee : state) :
  unit FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} ->
      defbinders
let __proj__Mkstate__item__lettys (projectee : state) :
  FStarC_Custard_Syntax.cty FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> lettys
let __proj__Mkstate__item__abbrevs (projectee : state) :
  (Prims.string Prims.list * FStarC_Custard_Syntax.cty) FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> abbrevs
let __proj__Mkstate__item__links (projectee : state) :
  FStarC_Custard_Unit.links=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> links
let __proj__Mkstate__item__imports (projectee : state) :
  (FStarC_Custard_Syntax.decl * FStarC_Custard_Syntax.type_info
    FStar_Pervasives_Native.option) Prims.list FStarC_Effect.ref=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> imports
let __proj__Mkstate__item__roots (projectee : state) :
  Prims.bool FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> roots
let __proj__Mkstate__item__nfe (projectee : state) :
  FStarC_Syntax_Syntax.sigelt FStarC_SMap.t=
  match projectee with
  | { deps; env; names; emitted; order; classes; bflags; counts; suffixes;
      fuel; chain; lifted; cur; cur_lid; chainlids; letdefs; effletdefs;
      defbinders; lettys; abbrevs; links; imports; roots; nfe;_} -> nfe
let float_probe_of_env (env : FStarC_TypeChecker_Env.env FStarC_Effect.ref)
  (ns : Prims.string Prims.list) :
  FStarC_Custard_Syntax.fwidth FStar_Pervasives_Native.option=
  let l =
    FStarC_Ident.lid_of_path (FStarC_List.op_At ns ["t"])
      FStarC_Range_Type.dummyRange in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang env in
    FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some se ->
      FStarC_Custard_Builtins.fwidth_of_attributes
        se.FStarC_Syntax_Syntax.sigattrs
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let init (deps : FStarC_Parser_Dep.deps) (env : FStarC_TypeChecker_Env.env) :
  state=
  let envr = FStarC_Effect.mk_ref env in
  FStarC_Custard_Builtins.set_float_probe (float_probe_of_env envr);
  (let uu___1 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___2 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___3 = FStarC_Effect.mk_ref [] in
   let uu___4 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___5 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___6 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___7 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___8 =
     let uu___9 = FStarC_Options.custard_fuel () in
     FStarC_Effect.mk_ref uu___9 in
   let uu___9 = FStarC_Effect.mk_ref [] in
   let uu___10 = FStarC_SMap.create (Prims.of_int 20) in
   let uu___11 =
     FStarC_Effect.mk_ref
       {
         FStarC_Custard_Syntax.ns = [];
         FStarC_Custard_Syntax.id = "custard";
         FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
       } in
   let uu___12 = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
   let uu___13 = FStarC_Effect.mk_ref [] in
   let uu___14 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___15 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___16 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___17 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___18 = FStarC_SMap.create (Prims.of_int 100) in
   let uu___19 =
     let uu___20 = FStarC_Options.custard_links () in
     FStarC_Custard_Unit.load_links uu___20 in
   let uu___20 = FStarC_Effect.mk_ref [] in
   let uu___21 = FStarC_SMap.create (Prims.of_int 20) in
   let uu___22 = FStarC_SMap.create (Prims.of_int 20) in
   {
     deps;
     env = envr;
     names = uu___1;
     emitted = uu___2;
     order = uu___3;
     classes = uu___4;
     bflags = uu___5;
     counts = uu___6;
     suffixes = uu___7;
     fuel = uu___8;
     chain = uu___9;
     lifted = uu___10;
     cur = uu___11;
     cur_lid = uu___12;
     chainlids = uu___13;
     letdefs = uu___14;
     effletdefs = uu___15;
     defbinders = uu___16;
     lettys = uu___17;
     abbrevs = uu___18;
     links = uu___19;
     imports = uu___20;
     roots = uu___21;
     nfe = uu___22
   })
let is_root (st : state) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_SMap.try_find st.roots (FStarC_Ident.string_of_lid l) in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
let local_inline_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.AllowUnboundUniverses; FStarC_TypeChecker_Env.Beta]
let custard_norm_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.DontUnfoldAttr [no_specialize_lid];
  FStarC_TypeChecker_Env.AllowUnboundUniverses;
  FStarC_TypeChecker_Env.EraseUniverses;
  FStarC_TypeChecker_Env.Beta;
  FStarC_TypeChecker_Env.Iota;
  FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
  FStarC_TypeChecker_Env.SafePrimops;
  FStarC_TypeChecker_Env.Eager_unfolding;
  FStarC_TypeChecker_Env.Inlining;
  FStarC_TypeChecker_Env.PureSubtermsWithinComputations;
  FStarC_TypeChecker_Env.Unascribe;
  FStarC_TypeChecker_Env.Unmeta;
  FStarC_TypeChecker_Env.ForExtraction;
  FStarC_TypeChecker_Env.UnfoldAttr
    [FStarC_Parser_Const.tcnorm_attr; FStarC_Parser_Const.tcmethod_lid];
  FStarC_TypeChecker_Env.ReduceProjections]
let tcenv (st : state) : FStarC_TypeChecker_Env.env=
  FStarC_Effect.op_Bang st.env
let chain_display_limit : Prims.int= Prims.of_int 10
let chain_entry_width : Prims.int= Prims.of_int 200
let clip_chain_entry (s : Prims.string) : Prims.string=
  if (FStarC_String.length s) <= chain_entry_width
  then s
  else
    (let uu___ = FStarC_String.substring s Prims.int_zero chain_entry_width in
     let uu___1 =
       let uu___2 =
         let uu___3 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_nat
             (FStarC_String.length s) in
         Prims.strcat uu___3 " chars)" in
       Prims.strcat " ... (" uu___2 in
     Prims.strcat uu___ uu___1)
let request_chain (st : state) : FStar_Pprint.document Prims.list=
  let uu___ = FStarC_Effect.op_Bang st.chain in
  match uu___ with
  | [] -> []
  | c ->
      let n = FStarC_List.length c in
      let uu___1 =
        if n <= chain_display_limit
        then (c, [])
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_int
                       (n - chain_display_limit) in
                   Prims.strcat uu___6 " more." in
                 Prims.strcat "... and " uu___5 in
               FStarC_Errors_Msg.text uu___4 in
             [uu___3] in
           ((FStar_Pervasives_Native.fst
               (FStarC_List.splitAt chain_display_limit c)), uu___2)) in
      (match uu___1 with
       | (shown, elided) ->
           let uu___2 =
             let uu___3 =
               FStarC_List.map
                 (fun s ->
                    let uu___4 =
                      let uu___5 = clip_chain_entry s in
                      Prims.strcat "  " uu___5 in
                    FStar_Pprint.doc_of_string uu___4) shown in
             FStarC_List.op_At uu___3 elided in
           FStarC_List.op_At [FStarC_Errors_Msg.text "Reached through:"]
             uu___2)
let custard_error (st : state) (code : FStarC_Errors_Codes.error_code)
  (msg : FStar_Pprint.document Prims.list) : 'a=
  let uu___ = let uu___1 = request_chain st in FStarC_List.op_At msg uu___1 in
  FStarC_Errors.raise_error0 code ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let custard_warning (st : state) (code : FStarC_Errors_Codes.error_code)
  (msg : FStar_Pprint.document Prims.list) : unit=
  let uu___ = let uu___1 = request_chain st in FStarC_List.op_At msg uu___1 in
  FStarC_Errors.log_issue0 code ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let truncate_msg (s : Prims.string) : Prims.string=
  if (FStarC_String.length s) <= (Prims.of_int 600)
  then s
  else
    (let uu___ = FStarC_String.substring s Prims.int_zero (Prims.of_int 600) in
     let uu___1 =
       let uu___2 =
         let uu___3 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_nat
             (FStarC_String.length s) in
         Prims.strcat uu___3 " chars)" in
       Prims.strcat " ... (" uu___2 in
     Prims.strcat uu___ uu___1)
let with_free_names (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list) : FStarC_TypeChecker_Env.env=
  FStarC_Custard_Prof.timed "env"
    (fun uu___ ->
       let uu___1 =
         FStarC_List.sortWith
           (fun a b ->
              a.FStarC_Syntax_Syntax.index - b.FStarC_Syntax_Syntax.index)
           bvs in
       FStarC_TypeChecker_Env.push_bvs env uu___1)
let env_for_term (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_TypeChecker_Env.env=
  let uu___ =
    let uu___1 = FStarC_Syntax_Free.names t in
    FStarC_Class_Setlike.elems
      (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv) uu___1 in
  with_free_names env uu___
let env_for_comp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : FStarC_TypeChecker_Env.env=
  let uu___ =
    let uu___1 = FStarC_Syntax_Free.names_comp c in
    FStarC_Class_Setlike.elems
      (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv) uu___1 in
  with_free_names env uu___
let norm_bounded_in (st : state) (env : FStarC_TypeChecker_Env.env)
  (what : Prims.string) (steps : FStarC_TypeChecker_Env.step Prims.list)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  try
    (fun uu___ ->
       match () with
       | () ->
           let env1 = env_for_term env t in
           FStarC_Custard_Prof.timed "norm"
             (fun uu___1 ->
                let uu___2 = FStarC_Options.custard_norm_budget () in
                FStarC_TypeChecker_Normalize.with_budget uu___2
                  (fun uu___3 ->
                     FStarC_TypeChecker_Normalize.normalize steps env1 t)))
      ()
  with
  | FStarC_TypeChecker_Normalize.Budget_exceeded ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_Options.custard_norm_budget () in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___6 in
              Prims.strcat uu___5
                (Prims.strcat " reduction steps) while normalizing "
                   (Prims.strcat what ".")) in
            Prims.strcat "Custard exceeded --custard_norm_budget (" uu___4 in
          FStarC_Errors_Msg.text uu___3 in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 = tcenv st in
                        FStarC_TypeChecker_Env.dsenv uu___11 in
                      FStarC_Syntax_Print.term_to_string' uu___10 t in
                    truncate_msg uu___9 in
                  Prims.strcat
                    "The term being normalized, before reduction, was: "
                    uu___8 in
                FStarC_Errors_Msg.text uu___7 in
              [uu___6] in
            (FStarC_Errors_Msg.text
               "Raising it is safe for a term that is merely large.  It is not a way to compile a term that truly diverges: past roughly 10^8 steps a deeply recursive reduction exhausts the normalizer's stack, and that is reported as a crash rather than as this error.")
              :: uu___5 in
          (FStarC_Errors_Msg.text
             "Reduction of an argument to a monomorphized binder need not terminate: a recursive definition reachable from it may unfold without bound. Either avoid specializing on this value, or raise --custard_norm_budget if the term is merely large.")
            :: uu___4 in
        uu___2 :: uu___3 in
      custard_error st FStarC_Errors_Codes.Error_CustardFuelExhausted uu___1
let norm_bounded (st : state) (what : Prims.string)
  (steps : FStarC_TypeChecker_Env.step Prims.list)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ = tcenv st in norm_bounded_in st uu___ what steps t
let norm_optional_in (env : FStarC_TypeChecker_Env.env)
  (steps : FStarC_TypeChecker_Env.step Prims.list)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 =
             FStarC_Custard_Prof.timed "norm"
               (fun uu___2 ->
                  let uu___3 = FStarC_Options.custard_norm_budget () in
                  FStarC_TypeChecker_Normalize.with_budget uu___3
                    (fun uu___4 ->
                       let uu___5 = env_for_term env t in
                       FStarC_TypeChecker_Normalize.normalize steps uu___5 t)) in
           FStar_Pervasives_Native.Some uu___1) ()
  with
  | FStarC_TypeChecker_Normalize.Budget_exceeded ->
      FStar_Pervasives_Native.None
let norm_optional (st : state)
  (steps : FStarC_TypeChecker_Env.step Prims.list)
  (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = tcenv st in norm_optional_in uu___ steps t
let nfe_steps (st : state) (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Util.extract_attr'
      FStarC_Parser_Const.normalize_for_extraction_lid
      se.FStarC_Syntax_Syntax.sigattrs in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some
      (uu___1, (steps, FStar_Pervasives_Native.None)::uu___2) ->
      let steps1 =
        let uu___3 = tcenv st in
        FStarC_TypeChecker_Normalize.normalize
          [FStarC_TypeChecker_Env.UnfoldUntil
             FStarC_Syntax_Syntax.delta_constant;
          FStarC_TypeChecker_Env.Zeta;
          FStarC_TypeChecker_Env.Iota;
          FStarC_TypeChecker_Env.Primops] uu___3 steps in
      let uu___3 =
        FStarC_TypeChecker_Primops_Base.try_unembed_simple
          (FStarC_Syntax_Embeddings.e_list
             FStarC_Syntax_Embeddings.e_norm_step) steps1 in
      (match uu___3 with
       | FStar_Pervasives_Native.Some steps2 ->
           let uu___4 = FStarC_TypeChecker_Cfg.translate_norm_steps steps2 in
           FStar_Pervasives_Native.Some uu___4
       | FStar_Pervasives_Native.None ->
           ((let uu___5 =
               let uu___6 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                   steps1 in
               FStarC_Format.fmt1
                 "Ill-formed application of 'normalize_for_extraction': normalization steps '%s' could not be interpreted"
                 uu___6 in
             FStarC_Errors.log_issue FStarC_Syntax_Syntax.has_range_sigelt se
               FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___5));
            FStar_Pervasives_Native.None))
  | FStar_Pervasives_Native.Some uu___1 ->
      (FStarC_Errors.log_issue FStarC_Syntax_Syntax.has_range_sigelt se
         FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic "Ill-formed application of 'normalize_for_extraction'");
       FStar_Pervasives_Native.None)
let fixup_normalize_for_extraction (st : state)
  (se : FStarC_Syntax_Syntax.sigelt) : FStarC_Syntax_Syntax.sigelt=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (is_rec, lbs);
        FStarC_Syntax_Syntax.lids1 = lids;_}
      when
      let uu___ =
        FStarC_Syntax_Util.extract_attr'
          FStarC_Parser_Const.normalize_for_extraction_lid
          se.FStarC_Syntax_Syntax.sigattrs in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> true
      | uu___1 -> false ->
      let key =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) lids in
      let uu___ = FStarC_SMap.try_find st.nfe key in
      (match uu___ with
       | FStar_Pervasives_Native.Some se1 -> se1
       | FStar_Pervasives_Native.None ->
           let se1 =
             let uu___1 = nfe_steps st se in
             match uu___1 with
             | FStar_Pervasives_Native.None -> se
             | FStar_Pervasives_Native.Some steps ->
                 let env =
                   let uu___2 = tcenv st in
                   {
                     FStarC_TypeChecker_Env.solver =
                       (uu___2.FStarC_TypeChecker_Env.solver);
                     FStarC_TypeChecker_Env.range =
                       (uu___2.FStarC_TypeChecker_Env.range);
                     FStarC_TypeChecker_Env.curmodule =
                       (uu___2.FStarC_TypeChecker_Env.curmodule);
                     FStarC_TypeChecker_Env.gamma =
                       (uu___2.FStarC_TypeChecker_Env.gamma);
                     FStarC_TypeChecker_Env.gamma_sig =
                       (uu___2.FStarC_TypeChecker_Env.gamma_sig);
                     FStarC_TypeChecker_Env.gamma_cache =
                       (uu___2.FStarC_TypeChecker_Env.gamma_cache);
                     FStarC_TypeChecker_Env.modules =
                       (uu___2.FStarC_TypeChecker_Env.modules);
                     FStarC_TypeChecker_Env.expected_typ =
                       (uu___2.FStarC_TypeChecker_Env.expected_typ);
                     FStarC_TypeChecker_Env.sigtab =
                       (uu___2.FStarC_TypeChecker_Env.sigtab);
                     FStarC_TypeChecker_Env.attrtab =
                       (uu___2.FStarC_TypeChecker_Env.attrtab);
                     FStarC_TypeChecker_Env.instantiate_imp =
                       (uu___2.FStarC_TypeChecker_Env.instantiate_imp);
                     FStarC_TypeChecker_Env.effects =
                       (uu___2.FStarC_TypeChecker_Env.effects);
                     FStarC_TypeChecker_Env.generalize =
                       (uu___2.FStarC_TypeChecker_Env.generalize);
                     FStarC_TypeChecker_Env.letrecs =
                       (uu___2.FStarC_TypeChecker_Env.letrecs);
                     FStarC_TypeChecker_Env.rec_names =
                       (uu___2.FStarC_TypeChecker_Env.rec_names);
                     FStarC_TypeChecker_Env.top_level =
                       (uu___2.FStarC_TypeChecker_Env.top_level);
                     FStarC_TypeChecker_Env.check_uvars =
                       (uu___2.FStarC_TypeChecker_Env.check_uvars);
                     FStarC_TypeChecker_Env.use_eq_strict =
                       (uu___2.FStarC_TypeChecker_Env.use_eq_strict);
                     FStarC_TypeChecker_Env.is_iface =
                       (uu___2.FStarC_TypeChecker_Env.is_iface);
                     FStarC_TypeChecker_Env.admit =
                       (uu___2.FStarC_TypeChecker_Env.admit);
                     FStarC_TypeChecker_Env.phase1 =
                       (uu___2.FStarC_TypeChecker_Env.phase1);
                     FStarC_TypeChecker_Env.failhard =
                       (uu___2.FStarC_TypeChecker_Env.failhard);
                     FStarC_TypeChecker_Env.flychecking =
                       (uu___2.FStarC_TypeChecker_Env.flychecking);
                     FStarC_TypeChecker_Env.uvar_subtyping =
                       (uu___2.FStarC_TypeChecker_Env.uvar_subtyping);
                     FStarC_TypeChecker_Env.intactics =
                       (uu___2.FStarC_TypeChecker_Env.intactics);
                     FStarC_TypeChecker_Env.nocoerce =
                       (uu___2.FStarC_TypeChecker_Env.nocoerce);
                     FStarC_TypeChecker_Env.tc_term =
                       (uu___2.FStarC_TypeChecker_Env.tc_term);
                     FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (uu___2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.universe_of =
                       (uu___2.FStarC_TypeChecker_Env.universe_of);
                     FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (uu___2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.teq_nosmt_force =
                       (uu___2.FStarC_TypeChecker_Env.teq_nosmt_force);
                     FStarC_TypeChecker_Env.subtype_nosmt_force =
                       (uu___2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                     FStarC_TypeChecker_Env.qtbl_name_and_index =
                       (uu___2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                     FStarC_TypeChecker_Env.fv_delta_depths =
                       (uu___2.FStarC_TypeChecker_Env.fv_delta_depths);
                     FStarC_TypeChecker_Env.proof_ns =
                       (uu___2.FStarC_TypeChecker_Env.proof_ns);
                     FStarC_TypeChecker_Env.synth_hook =
                       (uu___2.FStarC_TypeChecker_Env.synth_hook);
                     FStarC_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                     FStarC_TypeChecker_Env.splice =
                       (uu___2.FStarC_TypeChecker_Env.splice);
                     FStarC_TypeChecker_Env.mpreprocess =
                       (uu___2.FStarC_TypeChecker_Env.mpreprocess);
                     FStarC_TypeChecker_Env.postprocess =
                       (uu___2.FStarC_TypeChecker_Env.postprocess);
                     FStarC_TypeChecker_Env.identifier_info =
                       (uu___2.FStarC_TypeChecker_Env.identifier_info);
                     FStarC_TypeChecker_Env.tc_hooks =
                       (uu___2.FStarC_TypeChecker_Env.tc_hooks);
                     FStarC_TypeChecker_Env.dsenv =
                       (uu___2.FStarC_TypeChecker_Env.dsenv);
                     FStarC_TypeChecker_Env.nbe =
                       (uu___2.FStarC_TypeChecker_Env.nbe);
                     FStarC_TypeChecker_Env.strict_args_tab =
                       (uu___2.FStarC_TypeChecker_Env.strict_args_tab);
                     FStarC_TypeChecker_Env.disc_proj_tab =
                       (uu___2.FStarC_TypeChecker_Env.disc_proj_tab);
                     FStarC_TypeChecker_Env.erasable_types_tab =
                       (uu___2.FStarC_TypeChecker_Env.erasable_types_tab);
                     FStarC_TypeChecker_Env.enable_defer_to_tac =
                       (uu___2.FStarC_TypeChecker_Env.enable_defer_to_tac);
                     FStarC_TypeChecker_Env.unif_allow_ref_guards =
                       (uu___2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                     FStarC_TypeChecker_Env.erase_erasable_args = true;
                     FStarC_TypeChecker_Env.core_check =
                       (uu___2.FStarC_TypeChecker_Env.core_check);
                     FStarC_TypeChecker_Env.missing_decl =
                       (uu___2.FStarC_TypeChecker_Env.missing_decl);
                     FStarC_TypeChecker_Env.iface_todo =
                       (uu___2.FStarC_TypeChecker_Env.iface_todo);
                     FStarC_TypeChecker_Env.iface_hidden =
                       (uu___2.FStarC_TypeChecker_Env.iface_hidden);
                     FStarC_TypeChecker_Env.iface_lids =
                       (uu___2.FStarC_TypeChecker_Env.iface_lids);
                     FStarC_TypeChecker_Env.iface_val_lids =
                       (uu___2.FStarC_TypeChecker_Env.iface_val_lids)
                   } in
                 let norm_type =
                   FStarC_Syntax_Util.has_attribute
                     se.FStarC_Syntax_Syntax.sigattrs
                     FStarC_Parser_Const.normalize_for_extraction_type_lid in
                 let one lb =
                   let what =
                     let uu___2 =
                       let uu___3 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_either
                              FStarC_Syntax_Print.showable_bv
                              FStarC_Syntax_Syntax.showable_fv)
                           lb.FStarC_Syntax_Syntax.lbname in
                       Prims.strcat uu___3
                         ", as [@@normalize_for_extraction] asks" in
                     Prims.strcat "the definition of " uu___2 in
                   let lbdef =
                     norm_bounded_in st env what steps
                       lb.FStarC_Syntax_Syntax.lbdef in
                   let lbtyp =
                     if norm_type
                     then
                       norm_bounded_in st env
                         (Prims.strcat what " (its type)") steps
                         lb.FStarC_Syntax_Syntax.lbtyp
                     else lb.FStarC_Syntax_Syntax.lbtyp in
                   {
                     FStarC_Syntax_Syntax.lbname =
                       (lb.FStarC_Syntax_Syntax.lbname);
                     FStarC_Syntax_Syntax.lbunivs =
                       (lb.FStarC_Syntax_Syntax.lbunivs);
                     FStarC_Syntax_Syntax.lbtyp = lbtyp;
                     FStarC_Syntax_Syntax.lbeff =
                       (lb.FStarC_Syntax_Syntax.lbeff);
                     FStarC_Syntax_Syntax.lbdef = lbdef;
                     FStarC_Syntax_Syntax.lbattrs =
                       (lb.FStarC_Syntax_Syntax.lbattrs);
                     FStarC_Syntax_Syntax.lbpos =
                       (lb.FStarC_Syntax_Syntax.lbpos)
                   } in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_List.map one lbs in
                       (is_rec, uu___5) in
                     {
                       FStarC_Syntax_Syntax.lbs1 = uu___4;
                       FStarC_Syntax_Syntax.lids1 = lids
                     } in
                   FStarC_Syntax_Syntax.Sig_let uu___3 in
                 {
                   FStarC_Syntax_Syntax.sigel = uu___2;
                   FStarC_Syntax_Syntax.sigrng =
                     (se.FStarC_Syntax_Syntax.sigrng);
                   FStarC_Syntax_Syntax.sigquals =
                     (se.FStarC_Syntax_Syntax.sigquals);
                   FStarC_Syntax_Syntax.sigmeta =
                     (se.FStarC_Syntax_Syntax.sigmeta);
                   FStarC_Syntax_Syntax.sigattrs =
                     (se.FStarC_Syntax_Syntax.sigattrs);
                   FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                     (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                   FStarC_Syntax_Syntax.sigopts =
                     (se.FStarC_Syntax_Syntax.sigopts)
                 } in
           (FStarC_SMap.add st.nfe key se1; se1))
  | uu___ -> se
let type_matched_heads (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Ident.lident Prims.list=
  let acc = FStarC_Effect.mk_ref [] in
  let uu___ =
    FStarC_Syntax_Visit.visit_term false
      (fun t1 ->
         (let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress t1 in
            uu___3.FStarC_Syntax_Syntax.n in
          match uu___2 with
          | FStarC_Syntax_Syntax.Tm_match
              { FStarC_Syntax_Syntax.scrutinee = scrutinee;
                FStarC_Syntax_Syntax.ret_opt = uu___3;
                FStarC_Syntax_Syntax.brs = brs;
                FStarC_Syntax_Syntax.rc_opt1 = uu___4;_}
              ->
              let binds_type =
                FStarC_List.existsb
                  (fun uu___5 ->
                     match uu___5 with
                     | (p, uu___6, uu___7) ->
                         (match p.FStarC_Syntax_Syntax.v with
                          | FStarC_Syntax_Syntax.Pat_cons
                              (fv, uu___8, uu___9) ->
                              FStarC_Custard_Mono.ctor_stores_type env
                                (FStarC_Syntax_Syntax.lid_of_fv fv)
                          | uu___8 -> false)) brs in
              if binds_type
              then
                let uu___5 = FStarC_Syntax_Util.head_and_args_full scrutinee in
                (match uu___5 with
                 | (h, uu___6) ->
                     let uu___7 =
                       let uu___8 =
                         let uu___9 = FStarC_Syntax_Subst.compress h in
                         FStarC_Syntax_Util.un_uinst uu___9 in
                       uu___8.FStarC_Syntax_Syntax.n in
                     (match uu___7 with
                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                          let uu___8 =
                            let uu___9 = FStarC_Effect.op_Bang acc in
                            (FStarC_Syntax_Syntax.lid_of_fv fv) :: uu___9 in
                          FStarC_Effect.op_Colon_Equals acc uu___8
                      | uu___8 -> ()))
              else ()
          | uu___3 -> ());
         t1) t in
  FStarC_Effect.op_Bang acc
let ensure_lid_available (st : state) (l : FStarC_Ident.lident) : unit=
  let m = FStarC_Ident.nsstr l in
  let uu___ =
    if m <> ""
    then
      let uu___1 =
        let uu___2 = tcenv st in
        FStarC_Custard_Loader.module_is_loaded st.deps uu___2 m in
      Prims.not uu___1
    else false in
  if uu___
  then
    let uu___1 =
      FStarC_Custard_Prof.timed "load"
        (fun uu___2 ->
           let uu___3 = tcenv st in
           FStarC_Custard_Loader.ensure_loaded st.deps uu___3 m) in
    FStarC_Effect.op_Colon_Equals st.env uu___1
  else ()
let compile_time_demanded (st : state) (t : FStarC_Syntax_Syntax.term) :
  Prims.int Prims.list=
  let is_marked_app t1 =
    let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
    match uu___ with
    | (hd, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Subst.compress hd in
            FStarC_Syntax_Util.un_uinst uu___4 in
          uu___3.FStarC_Syntax_Syntax.n in
        (match uu___2 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             let l = FStarC_Syntax_Syntax.lid_of_fv fv in
             (ensure_lid_available st l;
              (let uu___4 = tcenv st in
               FStarC_TypeChecker_Env.fv_has_attr uu___4 fv
                 FStarC_Parser_Const.custard_compile_time_attr))
         | uu___3 -> false) in
  let contains_marked t1 =
    let found = FStarC_Effect.mk_ref false in
    let uu___ =
      FStarC_Syntax_Visit.visit_term false
        (fun t2 ->
           (let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Effect.op_Bang found in Prims.not uu___4 in
              if uu___3 then is_marked_app t2 else false in
            if uu___2 then FStarC_Effect.op_Colon_Equals found true else ());
           t2) t1 in
    FStarC_Effect.op_Bang found in
  let uu___ = FStarC_Syntax_Util.abs_formals t in
  match uu___ with
  | (bs, body, uu___1) ->
      let acc = FStarC_Effect.mk_ref [] in
      let add t1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Free.names t1 in
            FStarC_Class_Setlike.elems
              (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv)
              uu___4 in
          let uu___4 = FStarC_Effect.op_Bang acc in
          FStarC_List.op_At uu___3 uu___4 in
        FStarC_Effect.op_Colon_Equals acc uu___2 in
      let uu___2 =
        FStarC_Syntax_Visit.visit_term false
          (fun t1 ->
             (let uu___4 =
                let uu___5 = FStarC_Syntax_Subst.compress t1 in
                uu___5.FStarC_Syntax_Syntax.n in
              match uu___4 with
              | FStarC_Syntax_Syntax.Tm_app uu___5 ->
                  let uu___6 = is_marked_app t1 in
                  if uu___6 then add t1 else ()
              | FStarC_Syntax_Syntax.Tm_match
                  { FStarC_Syntax_Syntax.scrutinee = scrutinee;
                    FStarC_Syntax_Syntax.ret_opt = uu___5;
                    FStarC_Syntax_Syntax.brs = brs;
                    FStarC_Syntax_Syntax.rc_opt1 = uu___6;_}
                  ->
                  let uu___7 =
                    FStarC_List.existsb
                      (fun uu___8 ->
                         match uu___8 with
                         | (uu___9, uu___10, e) -> contains_marked e) brs in
                  if uu___7 then add scrutinee else ()
              | uu___5 -> ());
             t1) body in
      let names = FStarC_Effect.op_Bang acc in
      let uu___3 =
        FStarC_List.mapi
          (fun i b ->
             let uu___4 =
               FStarC_List.existsb
                 (fun v ->
                    FStarC_Syntax_Syntax.bv_eq v
                      b.FStarC_Syntax_Syntax.binder_bv) names in
             if uu___4 then [i] else []) bs in
      FStarC_List.flatten uu___3
let decl_only_attrs : (FStarC_Ident.lident * Prims.string) Prims.list=
  [(FStarC_Parser_Const.custard_extern_attr, "custard_extern");
  (FStarC_Parser_Const.custard_c_header_attr, "custard_c_header");
  (FStarC_Parser_Const.custard_opaque_attr, "custard_opaque");
  (FStarC_Parser_Const.custard_no_monomorphize_attr,
    "custard_no_monomorphize");
  (FStarC_Parser_Const.custard_compile_time_attr, "custard_compile_time");
  (FStarC_Parser_Const.custard_float_attr, "custard_float")]
let field_only_attrs : (FStarC_Ident.lident * Prims.string) Prims.list=
  [(FStarC_Parser_Const.custard_inline_field_attr, "custard_inline_field")]
let has_attr (a : FStarC_Ident.lident)
  (attrs : FStarC_Syntax_Syntax.term Prims.list) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.get_attribute a attrs in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
let c_decoration_flags (attrs : FStarC_Syntax_Syntax.term Prims.list) :
  FStarC_Custard_Syntax.flag Prims.list=
  let seen = FStarC_SMap.create (Prims.of_int 8) in
  let fresh k =
    let uu___ =
      let uu___1 = FStarC_SMap.try_find seen k in
      match uu___1 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___2 -> false in
    if uu___ then false else (FStarC_SMap.add seen k true; true) in
  FStarC_List.collect
    (fun a ->
       let a1 = FStarC_Syntax_Subst.compress a in
       let uu___ = FStarC_Syntax_Util.head_and_args_full a1 in
       match uu___ with
       | (head, args) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress head in
               uu___3.FStarC_Syntax_Syntax.n in
             (uu___2, args) in
           (match uu___1 with
            | (FStarC_Syntax_Syntax.Tm_fvar fv,
               ({
                  FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                    (FStarC_Const.Const_string (str, uu___2));
                  FStarC_Syntax_Syntax.pos = uu___3;
                  FStarC_Syntax_Syntax.hash_code = uu___4;_},
                uu___5)::[]) ->
                let nm =
                  FStarC_Ident.string_of_lid
                    (FStarC_Syntax_Syntax.lid_of_fv fv) in
                let uu___6 =
                  let uu___7 =
                    fresh (Prims.strcat nm (Prims.strcat "\000" str)) in
                  Prims.not uu___7 in
                if uu___6
                then []
                else
                  (match nm with
                   | "FStar.Attributes.Comment" ->
                       [FStarC_Custard_Syntax.Comment str]
                   | "FStar.Attributes.CPrologue" ->
                       [FStarC_Custard_Syntax.Prologue str]
                   | "FStar.Attributes.CEpilogue" ->
                       [FStarC_Custard_Syntax.Epilogue str]
                   | uu___7 -> [])
            | (FStarC_Syntax_Syntax.Tm_fvar fv,
               ({
                  FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                    (FStarC_Const.Const_string (a2, uu___2));
                  FStarC_Syntax_Syntax.pos = uu___3;
                  FStarC_Syntax_Syntax.hash_code = uu___4;_},
                uu___5)::({
                            FStarC_Syntax_Syntax.n =
                              FStarC_Syntax_Syntax.Tm_constant
                              (FStarC_Const.Const_string (b, uu___6));
                            FStarC_Syntax_Syntax.pos = uu___7;
                            FStarC_Syntax_Syntax.hash_code = uu___8;_},
                          uu___9)::[])
                ->
                let nm =
                  FStarC_Ident.string_of_lid
                    (FStarC_Syntax_Syntax.lid_of_fv fv) in
                let uu___10 =
                  let uu___11 =
                    fresh
                      (Prims.strcat nm
                         (Prims.strcat "\000"
                            (Prims.strcat a2 (Prims.strcat "\000" b)))) in
                  Prims.not uu___11 in
                if uu___10
                then []
                else
                  (match nm with
                   | "FStar.Attributes.custard_c_closure_prologue" ->
                       [FStarC_Custard_Syntax.ClosurePrologue (a2, b)]
                   | uu___11 -> [])
            | (FStarC_Syntax_Syntax.Tm_fvar fv, []) ->
                let nm =
                  FStarC_Ident.string_of_lid
                    (FStarC_Syntax_Syntax.lid_of_fv fv) in
                let uu___2 = let uu___3 = fresh nm in Prims.not uu___3 in
                if uu___2
                then []
                else
                  (match nm with
                   | "FStar.Attributes.CInline" ->
                       [FStarC_Custard_Syntax.CInline]
                   | "FStar.Attributes.CMacro" ->
                       [FStarC_Custard_Syntax.CMacro]
                   | uu___3 -> [])
            | uu___2 -> [])) attrs
let attr_home (nm : Prims.string) : Prims.string=
  match nm with
  | "custard_extern" ->
      "It replaces a definition by a reference to a hand-written one, so it goes on the [assume val] or [let] whose name the target realizes."
  | "custard_c_header" ->
      "It names the C header that declares an external symbol, so it goes beside the [@@custard_extern] it configures."
  | "custard_opaque" ->
      "It fixes a *type's* representation elsewhere, so it goes on the type."
  | "custard_no_monomorphize" ->
      "It says that a type class is not a compile-time dictionary, so it goes on the class."
  | "custard_compile_time" ->
      "It says that applications of a *definition* are to be evaluated during extraction, so it goes on that definition."
  | "custard_float" ->
      "It says that an abstract *type* is a floating-point format, so it goes on that type -- conventionally the [t] of the module that declares the arithmetic for it."
  | "custard_inline_field" ->
      "It asks for one field of a constructor to be stored by value, so it goes on that field."
  | uu___ -> ""
let report_attr (nm : Prims.string) (site : Prims.string)
  (why : Prims.string) : unit=
  FStarC_Errors.log_issue0
    FStarC_Errors_Codes.Warning_CustardIneffectiveAttribute ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
    (Obj.magic
       [FStarC_Errors_Msg.text
          (Prims.strcat "[@@"
             (Prims.strcat nm
                (Prims.strcat "] on " (Prims.strcat site " has no effect."))));
       FStarC_Errors_Msg.text why;
       FStarC_Errors_Msg.text (attr_home nm)])
let attributed_binders (se : FStarC_Syntax_Syntax.sigelt)
  (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.binder Prims.list=
  let merge bs_t bs_d =
    let at bs i =
      if i < (FStarC_List.length bs)
      then FStar_Pervasives_Native.Some (FStarC_List.nth bs i)
      else FStar_Pervasives_Native.None in
    let n =
      if (FStarC_List.length bs_t) > (FStarC_List.length bs_d)
      then FStarC_List.length bs_t
      else FStarC_List.length bs_d in
    let rec go i =
      if i >= n
      then []
      else
        (let b =
           let uu___ =
             let uu___1 = at bs_t i in
             let uu___2 = at bs_d i in (uu___1, uu___2) in
           match uu___ with
           | (FStar_Pervasives_Native.Some b1, FStar_Pervasives_Native.None)
               -> b1
           | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some b1)
               -> b1
           | (FStar_Pervasives_Native.Some b1, FStar_Pervasives_Native.Some
              c) ->
               let uu___1 =
                 let uu___2 =
                   FStarC_List.filter
                     (fun a ->
                        let uu___3 =
                          FStarC_List.existsb (FStarC_Syntax_Util.term_eq a)
                            b1.FStarC_Syntax_Syntax.binder_attrs in
                        Prims.not uu___3) c.FStarC_Syntax_Syntax.binder_attrs in
                 FStarC_List.op_At b1.FStarC_Syntax_Syntax.binder_attrs
                   uu___2 in
               {
                 FStarC_Syntax_Syntax.binder_bv =
                   (b1.FStarC_Syntax_Syntax.binder_bv);
                 FStarC_Syntax_Syntax.binder_qual =
                   (b1.FStarC_Syntax_Syntax.binder_qual);
                 FStarC_Syntax_Syntax.binder_positivity =
                   (b1.FStarC_Syntax_Syntax.binder_positivity);
                 FStarC_Syntax_Syntax.binder_attrs = uu___1
               }
           | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
               FStarC_Effect.failwith "unreachable" in
         let uu___ = go (i + Prims.int_one) in b :: uu___) in
    go Prims.int_zero in
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (uu___, lbs);
        FStarC_Syntax_Syntax.lids1 = uu___1;_}
      ->
      let uu___2 =
        FStarC_List.tryFind
          (fun lb ->
             match lb.FStarC_Syntax_Syntax.lbname with
             | FStar_Pervasives.Inr fv ->
                 FStarC_Ident.lid_equals (FStarC_Syntax_Syntax.lid_of_fv fv)
                   l
             | FStar_Pervasives.Inl uu___3 -> false) lbs in
      (match uu___2 with
       | FStar_Pervasives_Native.Some lb ->
           let uu___3 =
             FStarC_Syntax_Util.arrow_formals lb.FStarC_Syntax_Syntax.lbtyp in
           (match uu___3 with
            | (bs_t, uu___4) ->
                let uu___5 =
                  FStarC_Syntax_Util.abs_formals
                    lb.FStarC_Syntax_Syntax.lbdef in
                (match uu___5 with
                 | (bs_d, uu___6, uu___7) -> merge bs_t bs_d))
       | FStar_Pervasives_Native.None -> [])
  | FStarC_Syntax_Syntax.Sig_declare_typ
      { FStarC_Syntax_Syntax.lid2 = uu___; FStarC_Syntax_Syntax.us2 = uu___1;
        FStarC_Syntax_Syntax.t2 = t;_}
      ->
      let uu___2 = FStarC_Syntax_Util.arrow_formals t in
      FStar_Pervasives_Native.fst uu___2
  | uu___ -> []
let check_binder_attrs (kind : Prims.string) (owner : Prims.string)
  (b : FStarC_Syntax_Syntax.binder) : unit=
  FStarC_List.iter
    (fun uu___ ->
       match uu___ with
       | (a, nm) ->
           let uu___1 = has_attr a b.FStarC_Syntax_Syntax.binder_attrs in
           if uu___1
           then
             report_attr nm
               (Prims.strcat kind
                  (Prims.strcat " "
                     (Prims.strcat
                        (FStarC_Ident.string_of_id
                           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                        (Prims.strcat " of " owner))))
               "Custard reads this attribute off a declaration, never off a binder, so nothing consults it here."
           else ()) decl_only_attrs
let check_decl_attrs (l : FStarC_Ident.lident)
  (se : FStarC_Syntax_Syntax.sigelt) : unit=
  let owner = FStarC_Ident.string_of_lid l in
  let attrs = se.FStarC_Syntax_Syntax.sigattrs in
  FStarC_List.iter
    (fun uu___1 ->
       match uu___1 with
       | (a, nm) ->
           let uu___2 = has_attr a attrs in
           if uu___2
           then
             report_attr nm (Prims.strcat "the declaration " owner)
               "Custard reads this attribute off a constructor field, never off a declaration, so nothing consults it here."
           else ()) field_only_attrs;
  (let uu___2 =
     let uu___3 = has_attr FStarC_Parser_Const.custard_c_header_attr attrs in
     if uu___3
     then
       let uu___4 = has_attr FStarC_Parser_Const.custard_extern_attr attrs in
       Prims.not uu___4
     else false in
   if uu___2
   then
     report_attr "custard_c_header" (Prims.strcat "the declaration " owner)
       "The header is read only while building the rule that [@@custard_extern] asks for, and this declaration has no [@@custard_extern]."
   else ());
  (let uu___2 = attributed_binders se l in
   FStarC_List.iter (check_binder_attrs "the parameter" owner) uu___2)
let lookup_lid_typ (st : state) (l : FStarC_Ident.lident) :
  ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ) *
    FStarC_Range_Type.range) FStar_Pervasives_Native.option=
  ensure_lid_available st l;
  FStarC_Custard_Prof.timed "lookup"
    (fun uu___1 ->
       let uu___2 = tcenv st in
       FStarC_TypeChecker_Env.try_lookup_lid uu___2 l)
let unstub_lid (st : state) (l : FStarC_Ident.lident) : FStarC_Ident.lident=
  let ns =
    FStarC_List.map FStarC_Ident.string_of_id (FStarC_Ident.ns_of_lid l) in
  if Prims.not (FStarC_Custard_Builtins.is_stub_module ns)
  then l
  else
    (let uu___ =
       let uu___1 =
         FStarC_List.tryFind
           (fun uu___2 ->
              match uu___2 with
              | (a, uu___3) -> a = (FStarC_Ident.string_of_lid l))
           FStarC_Custard_Builtins.stub_aliases in
       match uu___1 with
       | FStar_Pervasives_Native.Some (uu___2, b) ->
           let p = FStarC_String.split [46] b in
           ((FStarC_List.init p), (FStarC_List.last p))
       | FStar_Pervasives_Native.None ->
           ((FStarC_Custard_Builtins.no_fstar_stubs ns),
             (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l))) in
     match uu___ with
     | (ns1, nm) ->
         let m = FStarC_String.concat "." ns1 in
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 = tcenv st in
               FStarC_Custard_Loader.module_is_loaded st.deps uu___4 m in
             if uu___3
             then true
             else
               (let uu___4 = FStarC_Custard_Loader.candidate_files st.deps m in
                match uu___4 with | hd::tl -> true | uu___5 -> false) in
           Prims.not uu___2 in
         if uu___1
         then l
         else
           (let l' =
              FStarC_Ident.lid_of_path (FStarC_List.op_At ns1 [nm])
                (FStarC_Ident.range_of_lid l) in
            ensure_lid_available st l';
            (let uu___3 =
               let uu___4 =
                 let uu___5 = tcenv st in
                 FStarC_TypeChecker_Env.lookup_qname uu___5 l' in
               match uu___4 with
               | FStar_Pervasives_Native.Some v -> true
               | uu___5 -> false in
             if uu___3 then l' else l)))
let name_of_lid (l : FStarC_Ident.lident) : FStarC_Custard_Syntax.name=
  let uu___ =
    let uu___1 =
      FStarC_List.map FStarC_Ident.string_of_id (FStarC_Ident.ns_of_lid l) in
    FStarC_Custard_Builtins.no_fstar_stubs uu___1 in
  {
    FStarC_Custard_Syntax.ns = uu___;
    FStarC_Custard_Syntax.id =
      (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l));
    FStarC_Custard_Syntax.spec = FStar_Pervasives_Native.None
  }
let name_of_bv (b : FStarC_Syntax_Syntax.bv) : Prims.string=
  FStarC_Custard_Syntax.uniq
    (FStarC_Ident.string_of_id b.FStarC_Syntax_Syntax.ppname)
    b.FStarC_Syntax_Syntax.index
let rename_let_name (top : FStarC_Syntax_Syntax.term)
  (lbattrs : FStarC_Syntax_Syntax.term Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Util.get_attribute FStarC_Parser_Const.rename_let_attr
      lbattrs in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some ((str, uu___1)::[]) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress str in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string
           (s, uu___3)) when s <> "" -> FStar_Pervasives_Native.Some s
       | uu___3 ->
           (FStarC_Errors.log_issue
              (FStarC_Syntax_Syntax.has_range_syntax ()) top
              FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic "Ignoring ill-formed application of `rename_let`");
            FStar_Pervasives_Native.None))
  | FStar_Pervasives_Native.Some uu___1 ->
      (FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ()) top
         FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic "Ignoring ill-formed application of `rename_let`");
       FStar_Pervasives_Native.None)
let rename_let_bv (top : FStarC_Syntax_Syntax.term)
  (b : FStarC_Syntax_Syntax.bv) (body : FStarC_Syntax_Syntax.term)
  (lbattrs : FStarC_Syntax_Syntax.term Prims.list) :
  (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term)=
  let uu___ = rename_let_name top lbattrs in
  match uu___ with
  | FStar_Pervasives_Native.None -> (b, body)
  | FStar_Pervasives_Native.Some s ->
      let b' =
        {
          FStarC_Syntax_Syntax.ppname =
            (FStarC_Ident.mk_ident
               (s, (FStarC_Ident.range_of_id b.FStarC_Syntax_Syntax.ppname)));
          FStarC_Syntax_Syntax.index = (b.FStarC_Syntax_Syntax.index);
          FStarC_Syntax_Syntax.sort = (b.FStarC_Syntax_Syntax.sort)
        } in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Syntax_Syntax.bv_to_name b' in (b, uu___5) in
            FStarC_Syntax_Syntax.NT uu___4 in
          [uu___3] in
        FStarC_Syntax_Subst.subst uu___2 body in
      (b', uu___1)
let rec datacon_headed (st : state) (t : FStarC_Syntax_Syntax.term) :
  Prims.bool=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Syntax_Subst.compress hd in
          FStarC_Syntax_Util.un_uinst uu___4 in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           let uu___3 =
             let uu___4 = tcenv st in
             FStarC_TypeChecker_Env.lookup_sigelt uu___4
               (FStarC_Syntax_Syntax.lid_of_fv fv) in
           (match uu___3 with
            | FStar_Pervasives_Native.Some se ->
                (match se.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_datacon _0 -> true
                 | uu___4 -> false)
            | FStar_Pervasives_Native.None -> false)
       | FStarC_Syntax_Syntax.Tm_abs
           { FStarC_Syntax_Syntax.b = uu___3;
             FStarC_Syntax_Syntax.body = body;
             FStarC_Syntax_Syntax.rc_opt = uu___4;_}
           -> datacon_headed st body
       | uu___3 -> false)
let rec hint_of_term (st : state) (fuel : Prims.int)
  (t : FStarC_Syntax_Syntax.term) :
  Prims.string FStar_Pervasives_Native.option=
  if fuel <= Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let sub ts = hints_of st (fuel - Prims.int_one) ts in
     let uu___ = FStarC_Syntax_Util.head_and_args_full t in
     match uu___ with
     | (hd, args) ->
         let uu___1 =
           let uu___2 =
             let uu___3 = FStarC_Syntax_Subst.compress hd in
             FStarC_Syntax_Util.un_uinst uu___3 in
           uu___2.FStarC_Syntax_Syntax.n in
         (match uu___1 with
          | FStarC_Syntax_Syntax.Tm_fvar fv when datacon_headed st hd ->
              FStar_Pervasives_Native.Some
                (FStarC_Ident.string_of_id
                   (FStarC_Ident.ident_of_lid
                      (FStarC_Syntax_Syntax.lid_of_fv fv)))
          | FStarC_Syntax_Syntax.Tm_fvar fv ->
              let h =
                FStarC_Ident.string_of_id
                  (FStarC_Ident.ident_of_lid
                     (FStarC_Syntax_Syntax.lid_of_fv fv)) in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_List.map FStar_Pervasives_Native.fst args in
                    sub uu___5 in
                  h :: uu___4 in
                FStarC_String.concat "_" uu___3 in
              FStar_Pervasives_Native.Some uu___2
          | FStarC_Syntax_Syntax.Tm_constant c ->
              (match c with
               | FStarC_Const.Const_int (v, uu___2) ->
                   let uu___3 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_int v in
                   FStar_Pervasives_Native.Some uu___3
               | FStarC_Const.Const_machine_int (v, uu___2, uu___3, uu___4)
                   ->
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_int v in
                   FStar_Pervasives_Native.Some uu___5
               | FStarC_Const.Const_bool b ->
                   FStar_Pervasives_Native.Some
                     (if b then "true" else "false")
               | FStarC_Const.Const_string (s, uu___2) ->
                   FStar_Pervasives_Native.Some s
               | FStarC_Const.Const_unit -> FStar_Pervasives_Native.None
               | uu___2 -> FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_abs
              { FStarC_Syntax_Syntax.b = uu___2;
                FStarC_Syntax_Syntax.body = body;
                FStarC_Syntax_Syntax.rc_opt = uu___3;_}
              -> hint_of_term st (fuel - Prims.int_one) body
          | FStarC_Syntax_Syntax.Tm_arrow uu___2 ->
              FStar_Pervasives_Native.Some "fn"
          | FStarC_Syntax_Syntax.Tm_type uu___2 ->
              FStar_Pervasives_Native.Some "type"
          | FStarC_Syntax_Syntax.Tm_refine
              { FStarC_Syntax_Syntax.b2 = b;
                FStarC_Syntax_Syntax.phi = uu___2;_}
              ->
              hint_of_term st (fuel - Prims.int_one)
                b.FStarC_Syntax_Syntax.sort
          | uu___2 -> FStar_Pervasives_Native.None))
and hints_of (st : state) (fuel : Prims.int)
  (ts : FStarC_Syntax_Syntax.term Prims.list) : Prims.string Prims.list=
  let hs =
    FStarC_List.collect
      (fun t ->
         let uu___ = hint_of_term st fuel t in
         match uu___ with
         | FStar_Pervasives_Native.Some s ->
             let uu___1 = let uu___2 = datacon_headed st t in (uu___2, s) in
             [uu___1]
         | FStar_Pervasives_Native.None -> []) ts in
  let uu___ =
    let uu___1 =
      FStarC_List.filter
        (fun uu___2 -> match uu___2 with | (dc, uu___3) -> Prims.not dc) hs in
    FStarC_List.map FStar_Pervasives_Native.snd uu___1 in
  match uu___ with
  | [] -> FStarC_List.map FStar_Pervasives_Native.snd hs
  | plain -> plain
let rec dedup (seen : Prims.string Prims.list) (hs : Prims.string Prims.list)
  : Prims.string Prims.list=
  match hs with
  | [] -> []
  | h::hs1 ->
      let uu___ = FStarC_List.existsb (fun s -> s = h) seen in
      if uu___
      then dedup seen hs1
      else (let uu___1 = dedup (h :: seen) hs1 in h :: uu___1)
let hint_width : Prims.int= Prims.of_int 48
let truncate_hint (h : Prims.string) : Prims.string=
  if (FStarC_String.length h) <= hint_width
  then h
  else FStarC_String.substring h Prims.int_zero hint_width
let rec fit (budget : Prims.int) (hs : Prims.string Prims.list) :
  Prims.string Prims.list=
  match hs with
  | [] -> []
  | h::hs1 ->
      let h1 = if budget < Prims.int_zero then truncate_hint h else h in
      let n = FStarC_String.length h1 in
      if (budget >= Prims.int_zero) && (n > budget)
      then []
      else
        (let uu___ =
           fit
             (((if budget < Prims.int_zero then hint_width else budget) - n)
                - Prims.int_one) hs1 in
         h1 :: uu___)
let hint_of_args (st : state)
  (args : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_List.map FStar_Pervasives_Native.snd args in
    hints_of st (Prims.of_int 3) uu___1 in
  match uu___ with
  | [] -> FStar_Pervasives_Native.None
  | hs ->
      let uu___1 =
        let uu___2 =
          let uu___3 = dedup [] hs in fit (Prims.of_int (-1)) uu___3 in
        FStarC_String.concat "_" uu___2 in
      FStar_Pervasives_Native.Some uu___1
let spec_suffix (st : state) (lstr : Prims.string)
  (args : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list) (n : Prims.int)
  : Prims.string FStar_Pervasives_Native.option=
  if match args with | [] -> true | uu___ -> false
  then FStar_Pervasives_Native.None
  else
    (let claim s =
       let key = Prims.strcat lstr (Prims.strcat "__" s) in
       let uu___ =
         let uu___1 = FStarC_SMap.try_find st.suffixes key in
         match uu___1 with
         | FStar_Pervasives_Native.Some v -> true
         | uu___2 -> false in
       if uu___ then false else (FStarC_SMap.add st.suffixes key true; true) in
     let rec fresh s k =
       if k > (Prims.of_int 1000)
       then s
       else
         (let uu___ = claim s in
          if uu___
          then s
          else
            (let uu___1 =
               let uu___2 =
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int k in
                 Prims.strcat "_" uu___3 in
               Prims.strcat s uu___2 in
             fresh uu___1 (k + Prims.int_one))) in
     let uu___ = hint_of_args st args in
     match uu___ with
     | FStar_Pervasives_Native.Some h when claim h ->
         FStar_Pervasives_Native.Some h
     | FStar_Pervasives_Native.Some h ->
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
               Prims.strcat "_" uu___4 in
             Prims.strcat h uu___3 in
           fresh uu___2 Prims.int_one in
         FStar_Pervasives_Native.Some uu___1
     | FStar_Pervasives_Native.None ->
         let uu___1 =
           let uu___2 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
           fresh uu___2 Prims.int_one in
         FStar_Pervasives_Native.Some uu___1)
let eff_of_comp (st : state) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Custard_Syntax.eff=
  let uu___ = tcenv st in FStarC_Custard_Effects.of_comp uu___ c
let unfold_abbrev (st : state) (ty : FStarC_Custard_Syntax.cty) :
  FStarC_Custard_Syntax.cty FStar_Pervasives_Native.option=
  match ty with
  | FStarC_Custard_Syntax.TApp (n, args) ->
      let uu___ =
        let uu___1 = FStarC_Custard_Syntax.string_of_name n in
        FStarC_SMap.try_find st.abbrevs uu___1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some (ps, body) ->
           let rec zip ps1 ts =
             match (ps1, ts) with
             | (p::ps2, t::ts1) -> (p, t) :: (zip ps2 ts1)
             | (p::ps2, []) -> (p, FStarC_Custard_Syntax.TAny) ::
                 (zip ps2 [])
             | ([], uu___1) -> [] in
           let uu___1 = FStarC_Custard_Syntax.subst_cty (zip ps args) body in
           FStar_Pervasives_Native.Some uu___1
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let rec head_ty (st : state) (ty : FStarC_Custard_Syntax.cty)
  (fuel : Prims.int) : FStarC_Custard_Syntax.cty=
  if fuel <= Prims.int_zero
  then ty
  else
    (let uu___ = unfold_abbrev st ty in
     match uu___ with
     | FStar_Pervasives_Native.Some ty' ->
         head_ty st ty' (fuel - Prims.int_one)
     | FStar_Pervasives_Native.None -> ty)
let rec apply_eff (st : state) (ty : FStarC_Custard_Syntax.cty)
  (n : Prims.int) : FStarC_Custard_Syntax.eff=
  if n <= Prims.int_zero
  then FStarC_Custard_Syntax.E_Pure
  else
    (match ty with
     | FStarC_Custard_Syntax.TArrow (uu___, e, r) ->
         let uu___1 = apply_eff st r (n - Prims.int_one) in
         FStarC_Custard_Syntax.join_eff e uu___1
     | uu___ ->
         let uu___1 = unfold_abbrev st ty in
         (match uu___1 with
          | FStar_Pervasives_Native.Some ty1 -> apply_eff st ty1 n
          | FStar_Pervasives_Native.None -> FStarC_Custard_Syntax.E_Impure))
let rec apply_result (st : state) (ty : FStarC_Custard_Syntax.cty)
  (n : Prims.int) : FStarC_Custard_Syntax.cty=
  if n <= Prims.int_zero
  then ty
  else
    (match ty with
     | FStarC_Custard_Syntax.TArrow (uu___, uu___1, r) ->
         apply_result st r (n - Prims.int_one)
     | uu___ ->
         let uu___1 = unfold_abbrev st ty in
         (match uu___1 with
          | FStar_Pervasives_Native.Some ty1 -> apply_result st ty1 n
          | FStar_Pervasives_Native.None -> FStarC_Custard_Syntax.TAny))
let note_abbrev (st : state) (d : FStarC_Custard_Syntax.decl) : unit=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      (match t.FStarC_Custard_Syntax.dt_body with
       | FStarC_Custard_Syntax.TAbbrev body ->
           let uu___ =
             FStarC_Custard_Syntax.string_of_name
               t.FStarC_Custard_Syntax.dt_name in
           FStarC_SMap.add st.abbrevs uu___
             ((t.FStarC_Custard_Syntax.dt_params), body)
       | uu___ -> ())
  | uu___ -> ()
let compile_time_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.AllowUnboundUniverses;
  FStarC_TypeChecker_Env.EraseUniverses;
  FStarC_TypeChecker_Env.Beta;
  FStarC_TypeChecker_Env.Iota;
  FStarC_TypeChecker_Env.Zeta;
  FStarC_TypeChecker_Env.SafePrimops;
  FStarC_TypeChecker_Env.Eager_unfolding;
  FStarC_TypeChecker_Env.Inlining;
  FStarC_TypeChecker_Env.Unascribe;
  FStarC_TypeChecker_Env.Unmeta;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant]
let is_c_backend (uu___ : unit) : Prims.bool=
  let b = FStarC_Options.custard_backend () in
  ((b = "C") || (b = "KrmlC")) || (b = "KrmlRust")
let c_realized_header (l : FStarC_Ident.lident) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      FStarC_List.map FStarC_Ident.string_of_id (FStarC_Ident.ns_of_lid l) in
    FStarC_Custard_Builtins.no_fstar_stubs uu___1 in
  FStarC_Custard_Builtins.c_realization_header uu___
let rec request (st : state) (k : spec_key) : FStarC_Custard_Syntax.name=
  FStarC_Custard_Prof.timed "request"
    (fun uu___ ->
       let k1 =
         let uu___1 = unstub_lid st k.sk_lid in
         {
           sk_lid = uu___1;
           sk_args = (k.sk_args);
           sk_subst = (k.sk_subst);
           sk_holes = (k.sk_holes)
         } in
       let key = string_of_key k1 in
       let uu___1 = FStarC_SMap.try_find st.names key in
       match uu___1 with
       | FStar_Pervasives_Native.Some nm -> nm
       | FStar_Pervasives_Native.None ->
           let uu___2 = import st key in
           (match uu___2 with
            | FStar_Pervasives_Native.Some nm -> nm
            | FStar_Pervasives_Native.None ->
                (check_budget st k1;
                 (let l = k1.sk_lid in
                  let lstr = FStarC_Ident.string_of_lid l in
                  let n =
                    let uu___4 = FStarC_SMap.try_find st.counts lstr in
                    match uu___4 with
                    | FStar_Pervasives_Native.None -> Prims.int_zero
                    | FStar_Pervasives_Native.Some n1 -> n1 in
                  FStarC_SMap.add st.counts lstr (n + Prims.int_one);
                  (let nm =
                     let uu___5 = name_of_lid l in
                     let uu___6 = spec_suffix st lstr k1.sk_args n in
                     {
                       FStarC_Custard_Syntax.ns =
                         (uu___5.FStarC_Custard_Syntax.ns);
                       FStarC_Custard_Syntax.id =
                         (uu___5.FStarC_Custard_Syntax.id);
                       FStarC_Custard_Syntax.spec = uu___6
                     } in
                   FStarC_SMap.add st.names key nm;
                   ensure_lid_available st l;
                   (let uu___7 = datacon_owner st l in
                    match uu___7 with
                    | FStar_Pervasives_Native.Some ty_lid when
                        FStarC_Ident.lid_equals ty_lid
                          FStarC_Parser_Const.exn_lid
                        ->
                        let d = extract_exn st l nm in
                        (FStarC_SMap.add st.emitted key d;
                         (let uu___10 =
                            let uu___11 = FStarC_Effect.op_Bang st.order in
                            key :: uu___11 in
                          FStarC_Effect.op_Colon_Equals st.order uu___10);
                         nm)
                    | FStar_Pervasives_Native.Some ty_lid ->
                        let uu___8 =
                          request st
                            {
                              sk_lid = ty_lid;
                              sk_args = [];
                              sk_subst = [];
                              sk_holes = Prims.int_zero
                            } in
                        nm
                    | FStar_Pervasives_Native.None ->
                        let saved = FStarC_Effect.op_Bang st.chain in
                        let saved_lids = FStarC_Effect.op_Bang st.chainlids in
                        (FStarC_Effect.op_Colon_Equals st.chain (key ::
                           saved);
                         FStarC_Effect.op_Colon_Equals st.chainlids (l ::
                           saved_lids);
                         (let d =
                            let uu___10 =
                              let uu___11 = clip_chain_entry key in
                              Prims.strcat "While extracting " uu___11 in
                            FStarC_Errors.with_ctx uu___10
                              (fun uu___11 ->
                                 FStarC_Custard_Prof.timed "extract_lid"
                                   (fun uu___12 ->
                                      extract_lid st l nm k1.sk_subst
                                        k1.sk_holes)) in
                          FStarC_Effect.op_Colon_Equals st.chain saved;
                          FStarC_Effect.op_Colon_Equals st.chainlids
                            saved_lids;
                          FStarC_SMap.add st.emitted key d;
                          note_abbrev st d;
                          (let uu___15 =
                             let uu___16 = FStarC_Effect.op_Bang st.order in
                             key :: uu___16 in
                           FStarC_Effect.op_Colon_Equals st.order uu___15);
                          nm))))))))
and import (st : state) (key : Prims.string) :
  FStarC_Custard_Syntax.name FStar_Pervasives_Native.option=
  let uu___ = FStarC_Custard_Unit.lookup st.links key in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (u, e) ->
      let imp =
        FStarC_Custard_Syntax.Imported (u, (e.FStarC_Custard_Unit.ue_home)) in
      let d =
        match e.FStarC_Custard_Unit.ue_decl with
        | FStarC_Custard_Syntax.DType dt ->
            FStarC_Custard_Syntax.DType
              {
                FStarC_Custard_Syntax.dt_name =
                  (dt.FStarC_Custard_Syntax.dt_name);
                FStarC_Custard_Syntax.dt_params =
                  (dt.FStarC_Custard_Syntax.dt_params);
                FStarC_Custard_Syntax.dt_body =
                  (dt.FStarC_Custard_Syntax.dt_body);
                FStarC_Custard_Syntax.dt_flags = (imp ::
                  (dt.FStarC_Custard_Syntax.dt_flags))
              }
        | FStarC_Custard_Syntax.DLet dl ->
            FStarC_Custard_Syntax.DLet
              {
                FStarC_Custard_Syntax.dl_name =
                  (dl.FStarC_Custard_Syntax.dl_name);
                FStarC_Custard_Syntax.dl_typars =
                  (dl.FStarC_Custard_Syntax.dl_typars);
                FStarC_Custard_Syntax.dl_binders =
                  (dl.FStarC_Custard_Syntax.dl_binders);
                FStarC_Custard_Syntax.dl_ret =
                  (dl.FStarC_Custard_Syntax.dl_ret);
                FStarC_Custard_Syntax.dl_eff =
                  (dl.FStarC_Custard_Syntax.dl_eff);
                FStarC_Custard_Syntax.dl_body =
                  (dl.FStarC_Custard_Syntax.dl_body);
                FStarC_Custard_Syntax.dl_flags = (imp ::
                  (dl.FStarC_Custard_Syntax.dl_flags))
              }
        | FStarC_Custard_Syntax.DExternal dx ->
            FStarC_Custard_Syntax.DExternal
              {
                FStarC_Custard_Syntax.dx_name =
                  (dx.FStarC_Custard_Syntax.dx_name);
                FStarC_Custard_Syntax.dx_typars =
                  (dx.FStarC_Custard_Syntax.dx_typars);
                FStarC_Custard_Syntax.dx_ty =
                  (dx.FStarC_Custard_Syntax.dx_ty);
                FStarC_Custard_Syntax.dx_target =
                  (dx.FStarC_Custard_Syntax.dx_target);
                FStarC_Custard_Syntax.dx_header =
                  (dx.FStarC_Custard_Syntax.dx_header);
                FStarC_Custard_Syntax.dx_flags = (imp ::
                  (dx.FStarC_Custard_Syntax.dx_flags))
              }
        | FStarC_Custard_Syntax.DExn de ->
            FStarC_Custard_Syntax.DExn
              {
                FStarC_Custard_Syntax.de_name =
                  (de.FStarC_Custard_Syntax.de_name);
                FStarC_Custard_Syntax.de_args =
                  (de.FStarC_Custard_Syntax.de_args);
                FStarC_Custard_Syntax.de_flags = (imp ::
                  (de.FStarC_Custard_Syntax.de_flags))
              } in
      let nm = FStarC_Custard_Syntax.name_of_decl d in
      (FStarC_SMap.add st.names key nm;
       FStarC_SMap.add st.emitted key d;
       note_abbrev st d;
       (let uu___5 =
          let uu___6 = FStarC_Effect.op_Bang st.imports in
          (d, (e.FStarC_Custard_Unit.ue_type)) :: uu___6 in
        FStarC_Effect.op_Colon_Equals st.imports uu___5);
       (let uu___6 = FStarC_Options.custard_dump_specializations () in
        if uu___6
        then FStarC_Format.print2 "Custard: %s comes from unit %s\n" key u
        else ());
       FStar_Pervasives_Native.Some nm)
and check_budget (st : state) (k : spec_key) : unit=
  FStarC_Custard_Prof.timed "budget"
    (fun uu___ ->
       let lstr = FStarC_Ident.string_of_lid k.sk_lid in
       let n =
         let uu___1 = FStarC_SMap.try_find st.counts lstr in
         match uu___1 with
         | FStar_Pervasives_Native.None -> Prims.int_zero
         | FStar_Pervasives_Native.Some n1 -> n1 in
       (let uu___2 =
          let uu___3 = FStarC_Options.custard_max_specializations () in
          n >= uu___3 in
        if uu___2
        then
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
                  Prims.strcat uu___7
                    (Prims.strcat " specializations of "
                       (Prims.strcat lstr
                          ", which is the limit set by --custard_max_specializations.")) in
                Prims.strcat "Custard created " uu___6 in
              FStarC_Errors_Msg.text uu___5 in
            [uu___4;
            FStarC_Errors_Msg.text
              "This usually means a definition recurses through a monomorphized binder. Use --custard_dump_specializations to see which definitions are being specialized."] in
          custard_error st FStarC_Errors_Codes.Error_CustardFuelExhausted
            uu___3
        else ());
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang st.fuel in
          uu___4 - Prims.int_one in
        FStarC_Effect.op_Colon_Equals st.fuel uu___3);
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang st.fuel in
          uu___4 <= Prims.int_zero in
        if uu___3
        then
          custard_error st FStarC_Errors_Codes.Error_CustardFuelExhausted
            [FStarC_Errors_Msg.text
               (Prims.strcat
                  "Custard ran out of specialization fuel while requesting "
                  (Prims.strcat lstr "; see --custard_fuel."))]
        else ()))
and extract_exn (st : state) (l : FStarC_Ident.lident)
  (nm : FStarC_Custard_Syntax.name) : FStarC_Custard_Syntax.decl=
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_datacon uu___1 l in
  match uu___ with
  | (uu___1, ty) ->
      let uu___2 = FStarC_Syntax_Util.arrow_formals_comp ty in
      (match uu___2 with
       | (bs, uu___3) ->
           let bs1 =
             let uu___4 =
               let uu___5 =
                 let uu___6 = tcenv st in
                 FStarC_Custard_Mono.is_erased_binder uu___6 in
               FStarC_List.map uu___5 bs in
             drop_flagged uu___4 bs in
           let uu___4 =
             let uu___5 =
               FStarC_List.map
                 (fun b ->
                    ty_of_typ st
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                 bs1 in
             {
               FStarC_Custard_Syntax.de_name = nm;
               FStarC_Custard_Syntax.de_args = uu___5;
               FStarC_Custard_Syntax.de_flags = []
             } in
           FStarC_Custard_Syntax.DExn uu___4)
and datacon_owner (st : state) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      {
        FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
          { FStarC_Syntax_Syntax.lid1 = uu___1;
            FStarC_Syntax_Syntax.us1 = uu___2;
            FStarC_Syntax_Syntax.t1 = uu___3;
            FStarC_Syntax_Syntax.ty_lid = ty_lid;
            FStarC_Syntax_Syntax.num_ty_params = uu___4;
            FStarC_Syntax_Syntax.mutuals1 = uu___5;
            FStarC_Syntax_Syntax.injective_type_params1 = uu___6;
            FStarC_Syntax_Syntax.proj_disc_lids = uu___7;_};
        FStarC_Syntax_Syntax.sigrng = uu___8;
        FStarC_Syntax_Syntax.sigquals = uu___9;
        FStarC_Syntax_Syntax.sigmeta = uu___10;
        FStarC_Syntax_Syntax.sigattrs = uu___11;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
        FStarC_Syntax_Syntax.sigopts = uu___13;_}
      -> FStar_Pervasives_Native.Some ty_lid
  | uu___1 -> FStar_Pervasives_Native.None
and binder_classes (st : state) (l : FStarC_Ident.lident) :
  FStarC_Custard_Mono.bclass Prims.list=
  FStarC_Custard_Prof.timed "binder_classes"
    (fun uu___ ->
       let key = FStarC_Ident.string_of_lid l in
       let uu___1 = FStarC_SMap.try_find st.classes key in
       match uu___1 with
       | FStar_Pervasives_Native.Some cs -> cs
       | FStar_Pervasives_Native.None ->
           (ensure_lid_available st l;
            (let attrs =
               let uu___3 =
                 let uu___4 = tcenv st in
                 FStarC_TypeChecker_Env.lookup_sigelt uu___4 l in
               match uu___3 with
               | FStar_Pervasives_Native.Some se ->
                   se.FStarC_Syntax_Syntax.sigattrs
               | FStar_Pervasives_Native.None -> [] in
             (let uu___4 =
                let uu___5 = tcenv st in
                FStarC_TypeChecker_Env.lookup_sigelt uu___5 l in
              match uu___4 with
              | FStar_Pervasives_Native.Some se -> check_decl_attrs l se
              | FStar_Pervasives_Native.None -> ());
             (let cs =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = tcenv st in
                    FStarC_TypeChecker_Env.lookup_sigelt uu___6 l in
                  FStarC_Option.map
                    (fun se ->
                       let uu___6 = fixup_normalize_for_extraction st se in
                       fixup_extract_as uu___6) uu___5 in
                match uu___4 with
                | FStar_Pervasives_Native.Some se ->
                    (match se.FStarC_Syntax_Syntax.sigel with
                     | FStarC_Syntax_Syntax.Sig_let
                         { FStarC_Syntax_Syntax.lbs1 = (uu___5, lbs);
                           FStarC_Syntax_Syntax.lids1 = uu___6;_}
                         ->
                         let uu___7 =
                           FStarC_List.tryFind
                             (fun lb ->
                                match lb.FStarC_Syntax_Syntax.lbname with
                                | FStar_Pervasives.Inr fv ->
                                    FStarC_Ident.lid_equals
                                      (FStarC_Syntax_Syntax.lid_of_fv fv) l
                                | FStar_Pervasives.Inl uu___8 -> false) lbs in
                         (match uu___7 with
                          | FStar_Pervasives_Native.Some lb ->
                              let uu___8 = tcenv st in
                              let uu___9 =
                                let uu___10 =
                                  compile_time_demanded st
                                    lb.FStarC_Syntax_Syntax.lbdef in
                                let uu___11 =
                                  template_demanded st
                                    lb.FStarC_Syntax_Syntax.lbtyp
                                    (FStar_Pervasives_Native.Some
                                       (lb.FStarC_Syntax_Syntax.lbdef)) in
                                FStarC_List.op_At uu___10 uu___11 in
                              FStarC_Custard_Mono.classify_def uu___8
                                (FStarC_List.op_At
                                   se.FStarC_Syntax_Syntax.sigattrs
                                   lb.FStarC_Syntax_Syntax.lbattrs)
                                lb.FStarC_Syntax_Syntax.lbtyp
                                (FStar_Pervasives_Native.Some
                                   (lb.FStarC_Syntax_Syntax.lbdef)) uu___9
                          | FStar_Pervasives_Native.None -> [])
                     | FStarC_Syntax_Syntax.Sig_declare_typ
                         { FStarC_Syntax_Syntax.lid2 = uu___5;
                           FStarC_Syntax_Syntax.us2 = uu___6;
                           FStarC_Syntax_Syntax.t2 = t;_}
                         ->
                         let uu___7 = tcenv st in
                         let uu___8 =
                           template_demanded st t
                             FStar_Pervasives_Native.None in
                         FStarC_Custard_Mono.classify_def uu___7
                           se.FStarC_Syntax_Syntax.sigattrs t
                           FStar_Pervasives_Native.None uu___8
                     | uu___5 -> [])
                | FStar_Pervasives_Native.None -> [] in
              let cs1 =
                if match cs with | hd::tl -> true | uu___4 -> false
                then cs
                else
                  (let uu___4 = lookup_lid_typ st l in
                   match uu___4 with
                   | FStar_Pervasives_Native.Some ((uu___5, ty), uu___6) ->
                       let uu___7 = tcenv st in
                       FStarC_Custard_Mono.classify uu___7 attrs ty
                   | FStar_Pervasives_Native.None -> []) in
              FStarC_SMap.add st.classes key cs1; cs1))))
and projector_of (st : state) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some se ->
      FStarC_List.tryPick
        (fun uu___1 ->
           match uu___1 with
           | FStarC_Syntax_Syntax.Projector (c, uu___2) ->
               FStar_Pervasives_Native.Some c
           | uu___2 -> FStar_Pervasives_Native.None)
        se.FStarC_Syntax_Syntax.sigquals
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
and ty_of_typ (st : state) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Custard_Syntax.cty=
  FStarC_Custard_Prof.timed "ty"
    (fun uu___ ->
       let t1 = FStarC_Syntax_Subst.compress t in
       match t1.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_bvar b ->
           let uu___1 = name_of_bv b in FStarC_Custard_Syntax.TVar uu___1
       | FStarC_Syntax_Syntax.Tm_name b ->
           let uu___1 =
             FStarC_Custard_Prof.timed "is_type_param"
               (fun uu___2 ->
                  let uu___3 = tcenv st in
                  FStarC_Custard_Mono.is_type_param uu___3
                    (FStarC_Syntax_Syntax.mk_binder b)) in
           if uu___1
           then
             let uu___2 = name_of_bv b in FStarC_Custard_Syntax.TVar uu___2
           else FStarC_Custard_Syntax.TAny
       | FStarC_Syntax_Syntax.Tm_uinst (t2, uu___1) -> ty_of_typ st t2
       | FStarC_Syntax_Syntax.Tm_fvar uu___1 when
           FStarC_Custard_Prof.timed "must_erase"
             (fun uu___2 ->
                let uu___3 = tcenv st in
                FStarC_TypeChecker_Util.must_erase_for_extraction uu___3 t1)
           -> FStarC_Custard_Syntax.TUnit
       | FStarC_Syntax_Syntax.Tm_app uu___1 when
           FStarC_Custard_Prof.timed "must_erase"
             (fun uu___2 ->
                let uu___3 = tcenv st in
                FStarC_TypeChecker_Util.must_erase_for_extraction uu___3 t1)
           -> FStarC_Custard_Syntax.TUnit
       | FStarC_Syntax_Syntax.Tm_fvar fv -> ty_of_fv st fv []
       | FStarC_Syntax_Syntax.Tm_arrow uu___1 ->
           let uu___2 = FStarC_Syntax_Util.arrow_formals_comp t1 in
           (match uu___2 with
            | (bs, c) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = tcenv st in
                    FStarC_Custard_Effects.is_reifiable uu___5
                      (FStarC_Syntax_Util.comp_effect_name c) in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = tcenv st in env_for_comp uu___8 c in
                        FStarC_Custard_Effects.reify_comp uu___7 c in
                      ty_of_typ st uu___6 in
                    (uu___5, FStarC_Custard_Syntax.E_Pure)
                  else
                    (let uu___5 =
                       let uu___6 =
                         let uu___7 = tcenv st in
                         FStarC_Custard_Effects.result_typ uu___7 c in
                       ty_of_typ st uu___6 in
                     let uu___6 = eff_of_comp st c in (uu___5, uu___6)) in
                (match uu___3 with
                 | (res, e) ->
                     let bs1 =
                       FStarC_Custard_Prof.timed "erased_binders"
                         (fun uu___4 ->
                            let uu___5 =
                              let uu___6 = tcenv st in
                              let uu___7 =
                                let uu___8 = tcenv st in
                                FStarC_Custard_Mono.erased_binders uu___8 t1 in
                              FStarC_Custard_Mono.keep_thunk uu___6 bs c
                                uu___7 in
                            drop_flagged uu___5 bs) in
                     let rec build bs2 =
                       match bs2 with
                       | [] -> res
                       | b::[] ->
                           let uu___4 =
                             let uu___5 =
                               ty_of_typ st
                                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                             (uu___5, e, res) in
                           FStarC_Custard_Syntax.TArrow uu___4
                       | b::bs3 ->
                           let uu___4 =
                             let uu___5 =
                               ty_of_typ st
                                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                             let uu___6 = build bs3 in
                             (uu___5, FStarC_Custard_Syntax.E_Pure, uu___6) in
                           FStarC_Custard_Syntax.TArrow uu___4 in
                     build bs1))
       | FStarC_Syntax_Syntax.Tm_app uu___1 ->
           let uu___2 =
             FStarC_Custard_Prof.timed "impure_result"
               (fun uu___3 ->
                  let uu___4 = tcenv st in
                  FStarC_Custard_Effects.impure_effect_result uu___4 t1) in
           (match uu___2 with
            | FStar_Pervasives_Native.Some a -> ty_of_typ st a
            | FStar_Pervasives_Native.None ->
                let uu___3 = FStarC_Syntax_Util.head_and_args_full t1 in
                (match uu___3 with
                 | (hd, args) ->
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Util.un_uinst hd in
                       uu___5.FStarC_Syntax_Syntax.n in
                     (match uu___4 with
                      | FStarC_Syntax_Syntax.Tm_fvar fv when
                          has_unrepresentable_param st
                            (FStarC_Syntax_Syntax.lid_of_fv fv)
                          ->
                          let t' =
                            norm_bounded st
                              "a higher-kinded type abbreviation"
                              [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                              FStarC_TypeChecker_Env.EraseUniverses;
                              FStarC_TypeChecker_Env.Beta;
                              FStarC_TypeChecker_Env.Iota;
                              FStarC_TypeChecker_Env.UnfoldOnly
                                [FStarC_Syntax_Syntax.lid_of_fv fv]] t1 in
                          let uu___5 = FStarC_Syntax_Util.term_eq t' t1 in
                          if uu___5
                          then FStarC_Custard_Syntax.TAny
                          else ty_of_typ st t'
                      | FStarC_Syntax_Syntax.Tm_abs uu___5 ->
                          let t' =
                            norm_bounded st "a type-level beta-redex"
                              [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                              FStarC_TypeChecker_Env.EraseUniverses;
                              FStarC_TypeChecker_Env.Beta] t1 in
                          let uu___6 = FStarC_Syntax_Util.term_eq t' t1 in
                          if uu___6
                          then FStarC_Custard_Syntax.TAny
                          else ty_of_typ st t'
                      | FStarC_Syntax_Syntax.Tm_fvar fv when
                          let uu___5 =
                            projector_of st
                              (FStarC_Syntax_Syntax.lid_of_fv fv) in
                          match uu___5 with
                          | FStar_Pervasives_Native.Some v -> true
                          | uu___6 -> false ->
                          let uu___5 =
                            norm_optional st
                              [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                              FStarC_TypeChecker_Env.EraseUniverses;
                              FStarC_TypeChecker_Env.Beta;
                              FStarC_TypeChecker_Env.Iota;
                              FStarC_TypeChecker_Env.Zeta;
                              FStarC_TypeChecker_Env.Weak;
                              FStarC_TypeChecker_Env.HNF;
                              FStarC_TypeChecker_Env.UnfoldUntil
                                FStarC_Syntax_Syntax.delta_constant] t1 in
                          (match uu___5 with
                           | FStar_Pervasives_Native.None ->
                               FStarC_Custard_Syntax.TAny
                           | FStar_Pervasives_Native.Some t' ->
                               let uu___6 = FStarC_Syntax_Util.term_eq t' t1 in
                               if uu___6
                               then FStarC_Custard_Syntax.TAny
                               else ty_of_typ st t')
                      | FStarC_Syntax_Syntax.Tm_name bv when
                          let uu___5 = tcenv st in
                          FStarC_Custard_Mono.is_value_indexed_arity uu___5
                            bv.FStarC_Syntax_Syntax.sort
                          ->
                          let uu___5 = name_of_bv bv in
                          FStarC_Custard_Syntax.TVar uu___5
                      | FStarC_Syntax_Syntax.Tm_fvar fv when
                          computes_type_from_values st
                            (FStarC_Syntax_Syntax.lid_of_fv fv) args
                          ->
                          let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                          let uu___5 =
                            norm_optional st
                              [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                              FStarC_TypeChecker_Env.EraseUniverses;
                              FStarC_TypeChecker_Env.Beta;
                              FStarC_TypeChecker_Env.Iota;
                              FStarC_TypeChecker_Env.Zeta;
                              FStarC_TypeChecker_Env.UnfoldOnly [l]] t1 in
                          (match uu___5 with
                           | FStar_Pervasives_Native.None ->
                               FStarC_Custard_Syntax.TAny
                           | FStar_Pervasives_Native.Some t' ->
                               let uu___6 = FStarC_Syntax_Util.term_eq t' t1 in
                               if uu___6
                               then FStarC_Custard_Syntax.TAny
                               else ty_of_typ st t')
                      | FStarC_Syntax_Syntax.Tm_fvar fv when
                          let uu___5 =
                            extern_template st
                              (FStarC_Syntax_Syntax.lid_of_fv fv) in
                          match uu___5 with
                          | FStar_Pervasives_Native.Some v -> true
                          | uu___6 -> false ->
                          let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                          let args1 =
                            FStarC_List.mapi
                              (fun i uu___5 ->
                                 match uu___5 with
                                 | (a, uu___6) -> template_arg st l i a) args in
                          let uu___5 =
                            let uu___6 =
                              request st
                                {
                                  sk_lid = l;
                                  sk_args = [];
                                  sk_subst = [];
                                  sk_holes = Prims.int_zero
                                } in
                            (uu___6, args1) in
                          FStarC_Custard_Syntax.TApp uu___5
                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                          let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                          let keep =
                            let uu___5 = lookup_lid_typ st l in
                            match uu___5 with
                            | FStar_Pervasives_Native.Some
                                ((uu___6, k), uu___7) ->
                                let uu___8 =
                                  let uu___9 =
                                    FStarC_Syntax_Util.arrow_formals k in
                                  FStar_Pervasives_Native.fst uu___9 in
                                FStarC_List.map
                                  (fun b ->
                                     let uu___9 = keeps_param st l b in
                                     Prims.not uu___9) uu___8
                            | FStar_Pervasives_Native.None -> [] in
                          let r =
                            let uu___5 =
                              let uu___6 = drop_flagged keep args in
                              FStarC_List.map FStar_Pervasives_Native.fst
                                uu___6 in
                            ty_of_fv st fv uu___5 in
                          if
                            Prims.not
                              (match r with
                               | FStarC_Custard_Syntax.TAny -> true
                               | uu___5 -> false)
                          then r
                          else
                            (let uu___5 =
                               norm_optional st
                                 [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                                 FStarC_TypeChecker_Env.EraseUniverses;
                                 FStarC_TypeChecker_Env.Beta;
                                 FStarC_TypeChecker_Env.Iota;
                                 FStarC_TypeChecker_Env.Zeta;
                                 FStarC_TypeChecker_Env.Weak;
                                 FStarC_TypeChecker_Env.HNF;
                                 FStarC_TypeChecker_Env.UnfoldUntil
                                   FStarC_Syntax_Syntax.delta_constant] t1 in
                             match uu___5 with
                             | FStar_Pervasives_Native.None ->
                                 FStarC_Custard_Syntax.TAny
                             | FStar_Pervasives_Native.Some t' ->
                                 let uu___6 =
                                   FStarC_Syntax_Util.term_eq t' t1 in
                                 if uu___6
                                 then FStarC_Custard_Syntax.TAny
                                 else ty_of_typ st t')
                      | uu___5 -> FStarC_Custard_Syntax.TAny)))
       | FStarC_Syntax_Syntax.Tm_abs uu___1 when
           let uu___2 = FStarC_Syntax_Util.abs_formals t1 in
           match uu___2 with
           | (bs, uu___3, uu___4) ->
               FStarC_List.for_all
                 (fun b ->
                    let uu___5 =
                      let uu___6 = tcenv st in
                      FStarC_Custard_Mono.is_type_binder uu___6 b in
                    Prims.not uu___5) bs
           ->
           let uu___2 = FStarC_Syntax_Util.abs_formals t1 in
           (match uu___2 with | (uu___3, body, uu___4) -> ty_of_typ st body)
       | FStarC_Syntax_Syntax.Tm_refine
           { FStarC_Syntax_Syntax.b2 = b;
             FStarC_Syntax_Syntax.phi = uu___1;_}
           -> ty_of_typ st b.FStarC_Syntax_Syntax.sort
       | FStarC_Syntax_Syntax.Tm_ascribed
           { FStarC_Syntax_Syntax.tm = tm; FStarC_Syntax_Syntax.asc = uu___1;
             FStarC_Syntax_Syntax.eff_opt = uu___2;_}
           -> ty_of_typ st tm
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = tm;
             FStarC_Syntax_Syntax.meta = uu___1;_}
           -> ty_of_typ st tm
       | FStarC_Syntax_Syntax.Tm_type uu___1 -> FStarC_Custard_Syntax.TAny
       | uu___1 -> FStarC_Custard_Syntax.TAny)
and has_unrepresentable_param (st : state) (l : FStarC_Ident.lident) :
  Prims.bool=
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      { FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let uu___1;
        FStarC_Syntax_Syntax.sigrng = uu___2;
        FStarC_Syntax_Syntax.sigquals = uu___3;
        FStarC_Syntax_Syntax.sigmeta = uu___4;
        FStarC_Syntax_Syntax.sigattrs = uu___5;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
        FStarC_Syntax_Syntax.sigopts = uu___7;_}
      ->
      let uu___8 = lookup_lid_typ st l in
      (match uu___8 with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some ((uu___9, k), uu___10) ->
           let uu___11 = FStarC_Syntax_Util.arrow_formals k in
           (match uu___11 with
            | (bs, uu___12) ->
                FStarC_Custard_Prof.timed "is_type_param"
                  (fun uu___13 ->
                     FStarC_List.existsb
                       (fun b ->
                          let uu___14 =
                            let uu___15 = tcenv st in
                            FStarC_Custard_Mono.is_type_binder uu___15 b in
                          if uu___14
                          then
                            let uu___15 =
                              let uu___16 = tcenv st in
                              FStarC_Custard_Mono.is_type_param uu___16 b in
                            Prims.not uu___15
                          else false) bs)))
  | uu___1 -> false
and computes_type_from_values (st : state) (l : FStarC_Ident.lident)
  (args : FStarC_Syntax_Syntax.args) : Prims.bool=
  match args with
  | [] -> false
  | uu___ ->
      let uu___1 =
        let uu___2 = tcenv st in
        FStarC_TypeChecker_Env.lookup_sigelt uu___2 l in
      (match uu___1 with
       | FStar_Pervasives_Native.Some
           {
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let uu___2;
             FStarC_Syntax_Syntax.sigrng = uu___3;
             FStarC_Syntax_Syntax.sigquals = uu___4;
             FStarC_Syntax_Syntax.sigmeta = uu___5;
             FStarC_Syntax_Syntax.sigattrs = uu___6;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
             FStarC_Syntax_Syntax.sigopts = uu___8;_}
           ->
           let uu___9 = lookup_lid_typ st l in
           (match uu___9 with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some ((uu___10, k), uu___11) ->
                let uu___12 = FStarC_Syntax_Util.arrow_formals k in
                (match uu___12 with
                 | (bs, uu___13) ->
                     let n = FStarC_List.length args in
                     FStarC_Custard_Prof.timed "is_type_param"
                       (fun uu___14 ->
                          let uu___15 =
                            FStarC_List.mapi (fun i b -> (i, b)) bs in
                          FStarC_List.existsb
                            (fun uu___16 ->
                               match uu___16 with
                               | (i, b) ->
                                   if i < n
                                   then
                                     let uu___17 =
                                       let uu___18 = tcenv st in
                                       FStarC_Custard_Mono.is_type_binder
                                         uu___18 b in
                                     Prims.not uu___17
                                   else false) uu___15)))
       | uu___2 -> false)
and keeps_param (st : state) (l : FStarC_Ident.lident)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  FStarC_Custard_Prof.timed "is_type_param"
    (fun uu___ ->
       let uu___1 = is_realized_type st l in
       if uu___1
       then
         let uu___2 = tcenv st in FStarC_Custard_Mono.is_type_binder uu___2 b
       else
         (let uu___2 = tcenv st in FStarC_Custard_Mono.is_type_param uu___2 b))
and is_realized_type (st : state) (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_Custard_Builtins.lookup_rule l in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_realized) ->
      true
  | uu___1 -> false
and has_builtin_type_rule (st : state) (t : FStarC_Syntax_Syntax.term) :
  Prims.bool=
  let uu___ = builtin_type_rules st t in
  match uu___ with | hd::tl -> true | uu___1 -> false
and builtin_type_rules (st : state) (t : FStarC_Syntax_Syntax.term) :
  Prims.string Prims.list= builtin_rules_at st (Prims.of_int 10) t
and builtin_rules_at (st : state) (fuel : Prims.int)
  (t : FStarC_Syntax_Syntax.term) : Prims.string Prims.list=
  let t0 =
    let uu___ = FStarC_Syntax_Util.unascribe t in
    FStarC_Syntax_Util.unmeta uu___ in
  let sub args =
    FStarC_List.collect
      (fun uu___ ->
         match uu___ with | (a, uu___1) -> builtin_rules_at st fuel a) args in
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t0 in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = b; FStarC_Syntax_Syntax.phi = uu___1;_} ->
      builtin_rules_at st fuel b.FStarC_Syntax_Syntax.sort
  | uu___1 ->
      let uu___2 = FStarC_Syntax_Util.head_and_args_full t0 in
      (match uu___2 with
       | (hd, args) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = FStarC_Syntax_Subst.compress hd in
               FStarC_Syntax_Util.un_uinst uu___5 in
             uu___4.FStarC_Syntax_Syntax.n in
           (match uu___3 with
            | FStarC_Syntax_Syntax.Tm_fvar fv ->
                let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                let uu___4 = FStarC_Custard_Builtins.lookup_rule l in
                (match uu___4 with
                 | FStar_Pervasives_Native.Some
                     (FStarC_Custard_Builtins.Rule_type uu___5) ->
                     let uu___6 = sub args in (FStarC_Ident.string_of_lid l)
                       :: uu___6
                 | uu___5 ->
                     let unfolded =
                       let uu___6 =
                         if fuel > Prims.int_zero
                         then FStarC_Syntax_CheckLN.is_ln t0
                         else false in
                       if uu___6
                       then
                         let uu___7 =
                           norm_optional st
                             [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                             FStarC_TypeChecker_Env.EraseUniverses;
                             FStarC_TypeChecker_Env.Beta;
                             FStarC_TypeChecker_Env.Iota;
                             FStarC_TypeChecker_Env.UnfoldOnly [l]] t0 in
                         match uu___7 with
                         | FStar_Pervasives_Native.Some t' ->
                             let uu___8 = FStarC_Syntax_Util.term_eq t' t0 in
                             (if uu___8
                              then FStar_Pervasives_Native.None
                              else FStar_Pervasives_Native.Some t')
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.None in
                     (match unfolded with
                      | FStar_Pervasives_Native.Some t' ->
                          builtin_rules_at st (fuel - Prims.int_one) t'
                      | FStar_Pervasives_Native.None -> sub args))
            | uu___4 -> sub args))
and template_index_names (st : state)
  (ts : FStarC_Syntax_Syntax.term Prims.list) :
  FStarC_Syntax_Syntax.bv Prims.list=
  let uu___ = template_index_scan st ts in FStar_Pervasives_Native.fst uu___
and template_index_scan (st : state)
  (ts : FStarC_Syntax_Syntax.term Prims.list) :
  (FStarC_Syntax_Syntax.bv Prims.list * Prims.string Prims.list)=
  let acc = FStarC_Effect.mk_ref [] in
  let seen = FStarC_Effect.mk_ref [] in
  let rec scan fuel t =
    let uu___ =
      FStarC_Syntax_Visit.visit_term false
        (fun t1 ->
           (let uu___2 =
              let uu___3 = FStarC_Syntax_Subst.compress t1 in
              uu___3.FStarC_Syntax_Syntax.n in
            match uu___2 with
            | FStarC_Syntax_Syntax.Tm_app uu___3 ->
                let uu___4 = FStarC_Syntax_Util.head_and_args_full t1 in
                (match uu___4 with
                 | (hd, args) ->
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStarC_Syntax_Subst.compress hd in
                         FStarC_Syntax_Util.un_uinst uu___7 in
                       uu___6.FStarC_Syntax_Syntax.n in
                     (match uu___5 with
                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                          let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                          (ensure_lid_available st l;
                           (let uu___7 = extern_template st l in
                            match uu___7 with
                            | FStar_Pervasives_Native.Some ps ->
                                let mentioned i =
                                  FStarC_List.existsb
                                    (fun p ->
                                       match p with
                                       | FStarC_Custard_Syntax.TP_arg j ->
                                           j = i
                                       | FStarC_Custard_Syntax.TP_lit uu___8
                                           -> false) ps in
                                FStarC_List.iteri
                                  (fun i uu___8 ->
                                     match uu___8 with
                                     | (a, uu___9) ->
                                         let uu___10 =
                                           let uu___11 = mentioned i in
                                           if uu___11
                                           then
                                             let uu___12 =
                                               let uu___13 = tcenv st in
                                               FStarC_Custard_Mono.is_type_term
                                                 uu___13 a in
                                             Prims.not uu___12
                                           else false in
                                         if uu___10
                                         then
                                           ((let uu___12 =
                                               let uu___13 =
                                                 let uu___14 =
                                                   let uu___15 =
                                                     let uu___16 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Class_Show.showable_int
                                                         i in
                                                     let uu___17 =
                                                       let uu___18 =
                                                         FStarC_Class_Show.show
                                                           FStarC_Syntax_Print.showable_term
                                                           a in
                                                       Prims.strcat " = "
                                                         uu___18 in
                                                     Prims.strcat uu___16
                                                       uu___17 in
                                                   Prims.strcat " argument "
                                                     uu___15 in
                                                 Prims.strcat
                                                   (FStarC_Ident.string_of_lid
                                                      l) uu___14 in
                                               let uu___14 =
                                                 FStarC_Effect.op_Bang seen in
                                               uu___13 :: uu___14 in
                                             FStarC_Effect.op_Colon_Equals
                                               seen uu___12);
                                            (let uu___12 =
                                               let uu___13 =
                                                 let uu___14 =
                                                   FStarC_Syntax_Free.names a in
                                                 FStarC_Class_Setlike.elems
                                                   (FStarC_FlatSet.setlike_flat_set
                                                      FStarC_Syntax_Syntax.ord_bv)
                                                   uu___14 in
                                               let uu___14 =
                                                 FStarC_Effect.op_Bang acc in
                                               FStarC_List.op_At uu___13
                                                 uu___14 in
                                             FStarC_Effect.op_Colon_Equals
                                               acc uu___12))
                                         else ()) args
                            | FStar_Pervasives_Native.None ->
                                let uu___8 =
                                  let uu___9 =
                                    if fuel > Prims.int_zero
                                    then FStarC_Syntax_CheckLN.is_ln t1
                                    else false in
                                  if uu___9
                                  then
                                    let uu___10 = tcenv st in
                                    FStarC_Custard_Mono.is_type_term uu___10
                                      t1
                                  else false in
                                if uu___8
                                then
                                  let uu___9 =
                                    norm_optional st
                                      [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                                      FStarC_TypeChecker_Env.EraseUniverses;
                                      FStarC_TypeChecker_Env.Beta;
                                      FStarC_TypeChecker_Env.Iota;
                                      FStarC_TypeChecker_Env.UnfoldOnly [l]]
                                      t1 in
                                  (match uu___9 with
                                   | FStar_Pervasives_Native.Some t' ->
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_Syntax_Util.term_eq t' t1 in
                                         Prims.not uu___11 in
                                       if uu___10
                                       then scan (fuel - Prims.int_one) t'
                                       else ()
                                   | FStar_Pervasives_Native.None -> ())
                                else ()))
                      | uu___6 -> ()))
            | uu___3 -> ());
           t1) t in
    () in
  FStarC_List.iter (scan (Prims.of_int 10)) ts;
  (let uu___1 = FStarC_Effect.op_Bang acc in
   let uu___2 =
     let uu___3 = FStarC_Effect.op_Bang seen in FStarC_List.rev uu___3 in
   (uu___1, uu___2))
and template_scan_terms (st : state) (t : FStarC_Syntax_Syntax.typ)
  (def : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term Prims.list)=
  let uu___ =
    match def with
    | FStar_Pervasives_Native.Some d ->
        let uu___1 = FStarC_Syntax_Util.abs_formals d in
        (match uu___1 with | (bs, body, uu___2) -> (bs, body))
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 = tcenv st in
          FStarC_Custard_Mono.arrow_formals_unfold uu___2 t in
        (match uu___1 with
         | (bs, comp) -> (bs, (FStarC_Syntax_Util.comp_result comp))) in
  match uu___ with
  | (bs, second) ->
      let uu___1 =
        let uu___2 =
          FStarC_List.map
            (fun b ->
               (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
            bs in
        FStarC_List.op_At uu___2 [second] in
      (bs, uu___1)
and template_demanded (st : state) (t : FStarC_Syntax_Syntax.typ)
  (def : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option) :
  Prims.int Prims.list=
  let uu___ = template_scan_terms st t def in
  match uu___ with
  | (bs, ts) ->
      let names = template_index_names st ts in
      let demanded =
        let uu___1 =
          FStarC_List.mapi
            (fun i b ->
               let uu___2 =
                 FStarC_List.existsb
                   (fun v ->
                      FStarC_Syntax_Syntax.bv_eq v
                        b.FStarC_Syntax_Syntax.binder_bv) names in
               if uu___2 then [i] else []) bs in
        FStarC_List.flatten uu___1 in
      (match def with
       | FStar_Pervasives_Native.Some uu___1 -> demanded
       | FStar_Pervasives_Native.None ->
           let leaves_runtime_param =
             let uu___1 =
               FStarC_List.mapi
                 (fun i b ->
                    if Prims.not (FStarC_List.mem i demanded)
                    then
                      let uu___2 =
                        let uu___3 = tcenv st in
                        FStarC_Custard_Mono.is_erased_binder uu___3 b in
                      Prims.not uu___2
                    else false) bs in
             FStarC_List.existsb (fun x -> x) uu___1 in
           let uu___1 =
             let uu___2 = tcenv st in
             FStarC_Custard_Mono.arrow_formals_unfold uu___2 t in
           (match uu___1 with
            | (uu___2, comp) ->
                let uu___3 =
                  if
                    (match demanded with | hd::tl -> true | uu___4 -> false)
                      && (Prims.not leaves_runtime_param)
                  then
                    let uu___4 =
                      FStarC_Syntax_Util.is_pure_or_ghost_comp comp in
                    Prims.not uu___4
                  else false in
                if uu___3 then [] else demanded))
and template_scan_report (st : state) (l : FStarC_Ident.lident) :
  (Prims.string Prims.list * Prims.string Prims.list * Prims.string
    Prims.list) FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      let uu___2 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___2 l in
    FStarC_Option.map
      (fun se ->
         let uu___2 = fixup_normalize_for_extraction st se in
         fixup_extract_as uu___2) uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.Some se ->
      let tdef =
        match se.FStarC_Syntax_Syntax.sigel with
        | FStarC_Syntax_Syntax.Sig_let
            { FStarC_Syntax_Syntax.lbs1 = (uu___1, lbs);
              FStarC_Syntax_Syntax.lids1 = uu___2;_}
            ->
            let uu___3 =
              FStarC_List.tryFind
                (fun lb ->
                   match lb.FStarC_Syntax_Syntax.lbname with
                   | FStar_Pervasives.Inr fv ->
                       FStarC_Ident.lid_equals
                         (FStarC_Syntax_Syntax.lid_of_fv fv) l
                   | FStar_Pervasives.Inl uu___4 -> false) lbs in
            (match uu___3 with
             | FStar_Pervasives_Native.Some lb ->
                 FStar_Pervasives_Native.Some
                   ((lb.FStarC_Syntax_Syntax.lbtyp),
                     (FStar_Pervasives_Native.Some
                        (lb.FStarC_Syntax_Syntax.lbdef)))
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        | FStarC_Syntax_Syntax.Sig_declare_typ
            { FStarC_Syntax_Syntax.lid2 = uu___1;
              FStarC_Syntax_Syntax.us2 = uu___2;
              FStarC_Syntax_Syntax.t2 = t;_}
            -> FStar_Pervasives_Native.Some (t, FStar_Pervasives_Native.None)
        | uu___1 -> FStar_Pervasives_Native.None in
      (match tdef with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some (t, def) ->
           let uu___1 = template_scan_terms st t def in
           (match uu___1 with
            | (bs, ts) ->
                let uu___2 = template_index_scan st ts in
                (match uu___2 with
                 | (names, apps) ->
                     let params =
                       FStarC_List.map
                         (fun b ->
                            FStarC_Ident.string_of_id
                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                         bs in
                     let uu___3 =
                       let uu___4 =
                         FStarC_List.map
                           (fun v ->
                              FStarC_Ident.string_of_id
                                v.FStarC_Syntax_Syntax.ppname) names in
                       (params, uu___4, apps) in
                     FStar_Pervasives_Native.Some uu___3)))
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
and extern_template (st : state) (l : FStarC_Ident.lident) :
  FStarC_Custard_Syntax.tmpl_piece Prims.list FStar_Pervasives_Native.option=
  let rule =
    let uu___ =
      let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
    match uu___ with
    | FStar_Pervasives_Native.Some se ->
        let uu___1 =
          FStarC_Custard_Builtins.rule_of_attributes
            se.FStarC_Syntax_Syntax.sigattrs in
        (match uu___1 with
         | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
         | FStar_Pervasives_Native.None ->
             FStarC_Custard_Builtins.lookup_rule l)
    | FStar_Pervasives_Native.None -> FStarC_Custard_Builtins.lookup_rule l in
  match rule with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_extern x) ->
      (match x.FStarC_Custard_Builtins.x_name with
       | FStar_Pervasives_Native.Some s ->
           let ps = FStarC_Custard_Syntax.template_of_string s in
           let uu___ = FStarC_Custard_Syntax.is_template ps in
           if uu___
           then FStar_Pervasives_Native.Some ps
           else FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
and const_of_arg (st : state) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Custard_Syntax.constant FStar_Pervasives_Native.option=
  let t1 =
    let uu___ =
      let uu___1 = FStarC_Syntax_Util.unlazy_emb t in
      FStarC_Syntax_Util.unascribe uu___1 in
    FStarC_Syntax_Util.unmeta uu___ in
  let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
  match uu___ with
  | (h, args) ->
      let args1 =
        FStarC_List.filter
          (fun uu___1 ->
             match uu___1 with
             | (a, uu___2) ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStarC_Syntax_Util.unlazy_emb a in
                         FStarC_Syntax_Util.unascribe uu___7 in
                       FStarC_Syntax_Util.unmeta uu___6 in
                     FStarC_Syntax_Subst.compress uu___5 in
                   uu___4.FStarC_Syntax_Syntax.n in
                 (match uu___3 with
                  | FStarC_Syntax_Syntax.Tm_constant
                      (FStarC_Const.Const_unit) -> false
                  | uu___4 -> true)) args in
      let inverse_pair a =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Syntax_Util.unlazy_emb a in
              FStarC_Syntax_Util.unascribe uu___4 in
            FStarC_Syntax_Util.unmeta uu___3 in
          FStarC_Syntax_Util.head_and_args_full uu___2 in
        match uu___1 with
        | (ih, uu___2) ->
            let uu___3 =
              let uu___4 = FStarC_Syntax_Subst.compress ih in
              uu___4.FStarC_Syntax_Syntax.n in
            (match uu___3 with
             | FStarC_Syntax_Syntax.Tm_fvar ifv ->
                 let inm =
                   FStarC_Ident.string_of_lid
                     (FStarC_Syntax_Syntax.lid_of_fv ifv) in
                 (((FStarC_Util.ends_with inm ".uint_to_t") ||
                     (FStarC_Util.ends_with inm ".int_to_t"))
                    || (FStarC_Util.ends_with inm ".__uint_to_t"))
                   || (FStarC_Util.ends_with inm ".__int_to_t")
             | uu___4 -> false) in
      let uu___1 =
        let uu___2 = FStarC_Syntax_Subst.compress h in
        uu___2.FStarC_Syntax_Syntax.n in
      (match uu___1 with
       | FStarC_Syntax_Syntax.Tm_constant c -> constant_of_sconst c
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           let nm =
             FStarC_Ident.string_of_lid (FStarC_Syntax_Syntax.lid_of_fv fv) in
           (match FStarC_List.rev args1 with
            | (a, uu___2)::uu___3 when
                (((((nm = "FStar.Ghost.hide") || (nm = "FStar.Ghost.reveal"))
                     || (FStarC_Util.ends_with nm ".uint_to_t"))
                    || (FStarC_Util.ends_with nm ".int_to_t"))
                   || (FStarC_Util.ends_with nm ".__uint_to_t"))
                  || (FStarC_Util.ends_with nm ".__int_to_t")
                -> const_of_arg st a
            | (a, uu___2)::uu___3 when
                if
                  (FStarC_Util.ends_with nm ".v") ||
                    (FStarC_Util.ends_with nm ".__v")
                then inverse_pair a
                else false -> const_of_arg st a
            | uu___2 -> FStar_Pervasives_Native.None)
       | uu___2 -> FStar_Pervasives_Native.None)
and extern_binder_names (st : state) (l : FStarC_Ident.lident) :
  Prims.string Prims.list=
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      {
        FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
          { FStarC_Syntax_Syntax.lid2 = uu___1;
            FStarC_Syntax_Syntax.us2 = uu___2; FStarC_Syntax_Syntax.t2 = t;_};
        FStarC_Syntax_Syntax.sigrng = uu___3;
        FStarC_Syntax_Syntax.sigquals = uu___4;
        FStarC_Syntax_Syntax.sigmeta = uu___5;
        FStarC_Syntax_Syntax.sigattrs = uu___6;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
        FStarC_Syntax_Syntax.sigopts = uu___8;_}
      ->
      let uu___9 =
        let uu___10 = tcenv st in
        FStarC_Custard_Mono.arrow_formals_unfold uu___10 t in
      (match uu___9 with
       | (bs, uu___10) ->
           FStarC_List.map
             (fun b ->
                FStarC_Ident.string_of_id
                  (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
             bs)
  | uu___1 -> []
and compiled_decl (st : state) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang st.chainlids in
  match uu___ with
  | h::uu___1 ->
      let uu___2 = FStarC_Effect.op_Bang st.cur_lid in
      (match uu___2 with
       | FStar_Pervasives_Native.Some c when FStarC_Ident.lid_equals c h ->
           FStar_Pervasives_Native.None
       | uu___3 -> FStar_Pervasives_Native.Some h)
  | [] -> FStar_Pervasives_Native.None
and name_provenance (st : state) (v : FStarC_Syntax_Syntax.bv) :
  Prims.string=
  let key =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      v.FStarC_Syntax_Syntax.index in
  let uu___ =
    let uu___1 = FStarC_SMap.try_find st.defbinders key in
    match uu___1 with
    | FStar_Pervasives_Native.Some v1 -> true
    | uu___2 -> false in
  if uu___
  then " (a binder of the definition being extracted)"
  else
    (let uu___1 = FStarC_SMap.try_find st.letdefs key in
     match uu___1 with
     | FStar_Pervasives_Native.Some d ->
         let uu___2 =
           let uu___3 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term d in
           Prims.strcat uu___3 ")" in
         Prims.strcat " (a local let, bound to: " uu___2
     | FStar_Pervasives_Native.None ->
         let uu___2 =
           let uu___3 = FStarC_SMap.try_find st.effletdefs key in
           match uu___3 with
           | FStar_Pervasives_Native.Some v1 -> true
           | uu___4 -> false in
         if uu___2
         then " (a local let bound to an effectful computation)"
         else
           " (not a binder of this definition, not a local let: it comes from a definition that was inlined away)")
and template_scan_diagnosis (st : state) (l : FStarC_Ident.lident)
  (a : FStarC_Syntax_Syntax.term) : FStar_Pprint.document Prims.list=
  let freev =
    let uu___ = FStarC_Syntax_Free.names a in
    FStarC_Class_Setlike.elems
      (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv) uu___ in
  let free =
    FStarC_List.map
      (fun v -> FStarC_Ident.string_of_id v.FStarC_Syntax_Syntax.ppname)
      freev in
  if match free with | [] -> true | uu___ -> false
  then []
  else
    (let dedup1 xs =
       FStarC_List.fold_left
         (fun acc x ->
            if FStarC_List.mem x acc then acc else FStarC_List.op_At acc [x])
         [] xs in
     let names = let uu___ = dedup1 free in FStarC_String.concat ", " uu___ in
     let scan_line who apps =
       if match apps with | [] -> true | uu___ -> false
       then
         FStarC_Errors_Msg.text
           (Prims.strcat "Rule 4d's scan of "
              (Prims.strcat who
                 " found no application of an external template at all, so it had nothing to demand from."))
       else
         (let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = dedup1 apps in
                    FStarC_String.concat "; " uu___5 in
                  Prims.strcat uu___4 "." in
                Prims.strcat " found: " uu___3 in
              Prims.strcat who uu___2 in
            Prims.strcat "Rule 4d's scan of " uu___1 in
          FStarC_Errors_Msg.text uu___) in
     let provenance =
       FStarC_List.map
         (fun v ->
            let uu___ =
              let uu___1 =
                let uu___2 = name_provenance st v in
                Prims.strcat
                  (FStarC_Ident.string_of_id v.FStarC_Syntax_Syntax.ppname)
                  uu___2 in
              Prims.strcat "  " uu___1 in
            FStarC_Errors_Msg.text uu___) freev in
     let uu___ = FStarC_Effect.op_Bang st.cur_lid in
     match uu___ with
     | FStar_Pervasives_Native.None ->
         [FStarC_Errors_Msg.text
            (Prims.strcat "The index mentions "
               (Prims.strcat names
                  ", and it is reached from a lifted local function, which rule 4d does not classify: only a top-level declaration's parameters can be demanded."))]
     | FStar_Pervasives_Native.Some cur ->
         let uu___1 = template_scan_report st cur in
         (match uu___1 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (params, demanded, apps) ->
              let dl = compiled_decl st in
              let ext =
                match dl with
                | FStar_Pervasives_Native.Some d -> extern_binder_names st d
                | FStar_Pervasives_Native.None -> [] in
              let owned =
                FStarC_List.filter (fun n -> FStarC_List.mem n params) free in
              let inext =
                FStarC_List.filter
                  (fun n ->
                     (Prims.not (FStarC_List.mem n params)) &&
                       (FStarC_List.mem n ext)) free in
              let orphan =
                FStarC_List.filter
                  (fun n ->
                     (Prims.not (FStarC_List.mem n params)) &&
                       (Prims.not (FStarC_List.mem n ext))) free in
              let missing =
                FStarC_List.filter
                  (fun n -> Prims.not (FStarC_List.mem n demanded)) owned in
              if (match orphan with | hd::tl -> true | uu___2 -> false)
              then
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = dedup1 orphan in
                          FStarC_String.concat ", " uu___7 in
                        Prims.strcat uu___6
                          (Prims.strcat ", which is a parameter of neither "
                             (Prims.strcat (FStarC_Ident.string_of_lid cur)
                                (Prims.strcat " nor "
                                   (Prims.strcat
                                      (match dl with
                                       | FStar_Pervasives_Native.Some d ->
                                           Prims.strcat
                                             "the declaration whose type is being compiled, "
                                             (FStarC_Ident.string_of_lid d)
                                       | FStar_Pervasives_Native.None ->
                                           "any other declaration: nothing else is being compiled here")
                                      ".")))) in
                      Prims.strcat "The index mentions " uu___5 in
                    FStarC_Errors_Msg.text uu___4 in
                  [uu___3;
                  FStarC_Errors_Msg.text
                    "So it came from a definition that was inlined into this one and whose binder outlived the inlining.  Rule 4d demands parameters of a declaration, and this is not one of either, so no demand it could have made would have reached it.";
                  FStarC_Errors_Msg.text "What Custard knows about the name:"] in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      scan_line (FStarC_Ident.string_of_lid cur) apps in
                    [uu___5] in
                  FStarC_List.op_At provenance uu___4 in
                FStarC_List.op_At uu___2 uu___3
              else
                if (match inext with | hd::tl -> true | uu___2 -> false)
                then
                  (let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = dedup1 inext in
                           FStarC_String.concat ", " uu___6 in
                         Prims.strcat uu___5
                           (Prims.strcat ", which is a parameter of "
                              (Prims.strcat
                                 (match dl with
                                  | FStar_Pervasives_Native.Some d ->
                                      FStarC_Ident.string_of_lid d
                                  | FStar_Pervasives_Native.None -> "?")
                                 ", the declaration whose type is being compiled here: its own codomain writes its own parameter into the template-id.")) in
                       Prims.strcat "The index mentions " uu___4 in
                     FStarC_Errors_Msg.text uu___3 in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         scan_line (FStarC_Ident.string_of_lid cur) apps in
                       [uu___5] in
                     (FStarC_Errors_Msg.text
                        "So the index was never substituted, and the caller's specialization cannot help: an external that writes its own parameter into a template-id has to have that parameter demanded on its own declaration.")
                       :: uu___4 in
                   uu___2 :: uu___3)
                else
                  if (match missing with | [] -> true | uu___2 -> false)
                  then
                    (let uu___2 =
                       let uu___3 =
                         scan_line (FStarC_Ident.string_of_lid cur) apps in
                       [uu___3;
                       FStarC_Errors_Msg.text
                         "So this declaration is monomorphic in it, and the value that is not constant was supplied by a caller rather than left behind here.  The request chain below is where to look."] in
                     (FStarC_Errors_Msg.text
                        (Prims.strcat "The index mentions "
                           (Prims.strcat names
                              (Prims.strcat
                                 ", which rule 4d did demand as compile-time known in "
                                 (Prims.strcat
                                    (FStarC_Ident.string_of_lid cur) ".")))))
                       :: uu___2)
                  else
                    (let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 = dedup1 missing in
                             FStarC_String.concat ", " uu___6 in
                           Prims.strcat uu___5
                             (Prims.strcat
                                ", which rule 4d did not demand as compile-time known in "
                                (Prims.strcat
                                   (FStarC_Ident.string_of_lid cur) ".")) in
                         Prims.strcat "The index mentions " uu___4 in
                       FStarC_Errors_Msg.text uu___3 in
                     let uu___3 =
                       let uu___4 =
                         scan_line (FStarC_Ident.string_of_lid cur) apps in
                       [uu___4;
                       FStarC_Errors_Msg.text
                         "Rule 4d demands a parameter when an application of the template is visible in that declaration's type or body.  A parameter it did not demand is one whose occurrence the scan did not recognise, which is a gap in Custard and not something the program can be rewritten around."] in
                     uu___2 :: uu___3)))
and template_arg (st : state) (l : FStarC_Ident.lident) (i : Prims.int)
  (a : FStarC_Syntax_Syntax.term) : FStarC_Custard_Syntax.cty=
  let uu___ =
    let uu___1 = tcenv st in FStarC_Custard_Mono.is_type_term uu___1 a in
  if uu___
  then ty_of_typ st a
  else
    (let a' =
       let uu___1 = norm_optional st compile_time_steps a in
       match uu___1 with
       | FStar_Pervasives_Native.Some t -> t
       | FStar_Pervasives_Native.None -> a in
     let a'1 = FStarC_Syntax_Util.unlazy_emb a' in
     let a'2 =
       let uu___1 = const_of_arg st a'1 in
       match uu___1 with
       | FStar_Pervasives_Native.Some uu___2 -> a'1
       | FStar_Pervasives_Native.None ->
           let u = unfold_lets st (Prims.of_int 100) a'1 in
           let uu___2 = FStarC_Syntax_Util.term_eq u a'1 in
           if uu___2
           then a'1
           else
             (let uu___3 = norm_optional st compile_time_steps u in
              match uu___3 with
              | FStar_Pervasives_Native.Some t ->
                  FStarC_Syntax_Util.unlazy_emb t
              | FStar_Pervasives_Native.None ->
                  FStarC_Syntax_Util.unlazy_emb u) in
     let uu___1 = const_of_arg st a'2 in
     match uu___1 with
     | FStar_Pervasives_Native.Some c -> FStarC_Custard_Syntax.TConst c
     | FStar_Pervasives_Native.None ->
         ((let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_Show.show FStarC_Class_Show.showable_int
                         i in
                     Prims.strcat uu___8
                       (Prims.strcat " of the external type "
                          (Prims.strcat (FStarC_Ident.string_of_lid l)
                             " is a value, and it does not reduce to a constant.")) in
                   Prims.strcat "Custard: argument " uu___7 in
                 FStarC_Errors_Msg.text uu___6 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 =
                     let uu___9 =
                       let uu___10 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term a'2 in
                       Prims.strcat "What it reduced to was: " uu___10 in
                     FStarC_Errors_Msg.text uu___9 in
                   let uu___9 =
                     let uu___10 =
                       let uu___11 =
                         let uu___12 =
                           let uu___13 =
                             let uu___14 = FStarC_Effect.op_Bang st.cur in
                             FStarC_Custard_Syntax.string_of_name uu___14 in
                           Prims.strcat uu___13
                             ", which is where the index is still a runtime value." in
                         Prims.strcat "It is reached while extracting "
                           uu___12 in
                       FStarC_Errors_Msg.text uu___11 in
                     [uu___10] in
                   uu___8 :: uu___9 in
                 (FStarC_Errors_Msg.text
                    "The target spelling of this type is a template, so its arguments are written into a template-id; a non-type template argument has to be a constant expression, and one that is only known at run time is not.")
                   :: uu___7 in
               uu___5 :: uu___6 in
             let uu___5 =
               let uu___6 = template_scan_diagnosis st l a'2 in
               FStarC_List.op_At uu___6
                 [FStarC_Errors_Msg.text
                    "Either make the argument compile-time known, or drop the placeholder for it from the [@@custard_extern] string, which makes the argument invisible to the target."] in
             FStarC_List.op_At uu___4 uu___5 in
           custard_error st FStarC_Errors_Codes.Error_CustardBadTemplateArg
             uu___3);
          FStarC_Custard_Syntax.TAny))
and ty_of_fv (st : state) (fv : FStarC_Syntax_Syntax.fv)
  (args : FStarC_Syntax_Syntax.term Prims.list) : FStarC_Custard_Syntax.cty=
  let l = FStarC_Syntax_Syntax.lid_of_fv fv in
  if FStarC_Ident.lid_equals l FStarC_Parser_Const.unit_lid
  then FStarC_Custard_Syntax.TUnit
  else
    (let args1 = FStarC_List.map (ty_of_typ st) args in
     let uu___ = FStarC_Custard_Builtins.lookup_rule l in
     match uu___ with
     | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_type f) ->
         f args1
     | uu___1 ->
         let uu___2 =
           let uu___3 =
             request st
               {
                 sk_lid = l;
                 sk_args = [];
                 sk_subst = [];
                 sk_holes = Prims.int_zero
               } in
           (uu___3, args1) in
         FStarC_Custard_Syntax.TApp uu___2)
and constant_of_sconst (c : FStarC_Const.sconst) :
  FStarC_Custard_Syntax.constant FStar_Pervasives_Native.option=
  match c with
  | FStarC_Const.Const_unit ->
      FStar_Pervasives_Native.Some FStarC_Custard_Syntax.CUnit
  | FStarC_Const.Const_bool b ->
      FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.CBool b)
  | FStarC_Const.Const_int (v, b) ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.CInt (v, b, FStar_Pervasives_Native.None))
  | FStarC_Const.Const_machine_int (v, b, sg, w) ->
      FStar_Pervasives_Native.Some
        (FStarC_Custard_Syntax.CInt
           (v, b,
             (FStar_Pervasives_Native.Some
                (sg, (FStarC_Custard_Syntax.iwidth_of_width w)))))
  | FStarC_Const.Const_char c1 ->
      FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.CChar c1)
  | FStarC_Const.Const_string (s, uu___) ->
      FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.CString s)
  | uu___ -> FStar_Pervasives_Native.None
and ty_of_constant (st : state) (c : FStarC_Custard_Syntax.constant) :
  FStarC_Custard_Syntax.cty=
  let prim l =
    let uu___ =
      let uu___1 =
        request st
          {
            sk_lid = l;
            sk_args = [];
            sk_subst = [];
            sk_holes = Prims.int_zero
          } in
      (uu___1, []) in
    FStarC_Custard_Syntax.TApp uu___ in
  match c with
  | FStarC_Custard_Syntax.CUnit -> FStarC_Custard_Syntax.TUnit
  | FStarC_Custard_Syntax.CBool uu___ -> prim FStarC_Parser_Const.bool_lid
  | FStarC_Custard_Syntax.CInt (uu___, uu___1, FStar_Pervasives_Native.None)
      -> prim FStarC_Parser_Const.int_lid
  | FStarC_Custard_Syntax.CInt
      (uu___, uu___1, FStar_Pervasives_Native.Some sw) ->
      FStarC_Custard_Syntax.TInt sw
  | FStarC_Custard_Syntax.CFloat (uu___, fw) ->
      FStarC_Custard_Syntax.TFloat fw
  | FStarC_Custard_Syntax.CChar uu___ -> prim FStarC_Parser_Const.char_lid
  | FStarC_Custard_Syntax.CString uu___ ->
      prim FStarC_Parser_Const.string_lid
and is_data_ctor (fv : FStarC_Syntax_Syntax.fv) : Prims.bool=
  match fv.FStarC_Syntax_Syntax.fv_qual with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Data_ctor) -> true
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Record_ctor uu___) ->
      true
  | uu___ -> false
and compile_time_head (st : state) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.head_and_args_full t in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Syntax_Subst.compress hd in
          FStarC_Syntax_Util.un_uinst uu___4 in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           let l = FStarC_Syntax_Syntax.lid_of_fv fv in
           (ensure_lid_available st l;
            (let uu___4 =
               let uu___5 = tcenv st in
               FStarC_TypeChecker_Env.fv_has_attr uu___5 fv
                 FStarC_Parser_Const.custard_compile_time_attr in
             if uu___4
             then FStar_Pervasives_Native.Some l
             else FStar_Pervasives_Native.None))
       | uu___3 -> FStar_Pervasives_Native.None)
and expr_of_term (st : state) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Custard_Syntax.expr=
  FStarC_Custard_Prof.timed "expr"
    (fun uu___ ->
       let t1 =
         let uu___1 = FStarC_Syntax_Util.unlazy_emb t in
         FStarC_Syntax_Subst.compress uu___1 in
       let t2 =
         let uu___1 = compile_time_head st t1 in
         match uu___1 with
         | FStar_Pervasives_Native.None -> t1
         | FStar_Pervasives_Native.Some l ->
             let free = FStarC_Syntax_Free.names t1 in
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Setlike.is_empty
                   (FStarC_FlatSet.setlike_flat_set
                      FStarC_Syntax_Syntax.ord_bv) free in
               Prims.not uu___3 in
             if uu___2
             then
               let uu___3 =
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               FStarC_Class_Setlike.elems
                                 (FStarC_FlatSet.setlike_flat_set
                                    FStarC_Syntax_Syntax.ord_bv) free in
                             FStarC_List.map
                               (fun b ->
                                  FStarC_Class_Show.show
                                    FStarC_Ident.showable_ident
                                    b.FStarC_Syntax_Syntax.ppname) uu___10 in
                           FStarC_String.concat ", " uu___9 in
                         Prims.strcat uu___8 "." in
                       Prims.strcat
                         "The attribute is a promise that every application is known at extraction time; this one is not, because it mentions "
                         uu___7 in
                     FStarC_Errors_Msg.text uu___6 in
                   [uu___5;
                   FStarC_Errors_Msg.text
                     "Either the definition should be compiled rather than evaluated, in which case remove the attribute, or the caller should be applying it to a constant."] in
                 (FStarC_Errors_Msg.text
                    (Prims.strcat (FStarC_Ident.string_of_lid l)
                       " is marked [@@custard_compile_time], but this application of it depends on a runtime value."))
                   :: uu___4 in
               custard_error st
                 FStarC_Errors_Codes.Error_CustardNotCompileTime uu___3
             else
               (let t' =
                  norm_bounded st
                    (Prims.strcat "an application of "
                       (FStarC_Ident.string_of_lid l)) compile_time_steps t1 in
                let uu___3 = compile_time_head st t' in
                match uu___3 with
                | FStar_Pervasives_Native.Some uu___4 ->
                    custard_error st
                      FStarC_Errors_Codes.Error_CustardNotCompileTime
                      [FStarC_Errors_Msg.text
                         (Prims.strcat (FStarC_Ident.string_of_lid l)
                            " is marked [@@custard_compile_time], but this application of it does not reduce, although its arguments are all known.");
                      FStarC_Errors_Msg.text
                        "Some definition it needs is abstract in the interface it was loaded through."]
                | FStar_Pervasives_Native.None ->
                    let uu___4 = FStarC_Syntax_Util.unlazy_emb t' in
                    FStarC_Syntax_Subst.compress uu___4) in
       match t2.FStarC_Syntax_Syntax.n with
       | FStarC_Syntax_Syntax.Tm_constant c ->
           let uu___1 = constant_of_sconst c in
           (match uu___1 with
            | FStar_Pervasives_Native.Some c1 ->
                let uu___2 = ty_of_constant st c1 in
                FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EConst c1)
                  uu___2 FStarC_Custard_Syntax.E_Pure
            | FStar_Pervasives_Native.None -> FStarC_Custard_Syntax.unit_expr)
       | FStarC_Syntax_Syntax.Tm_bvar b ->
           let uu___1 = lifted_ref st b in
           (match uu___1 with
            | FStar_Pervasives_Native.Some e -> e
            | FStar_Pervasives_Native.None ->
                let ty = ty_of_typ st b.FStarC_Syntax_Syntax.sort in
                let ty1 =
                  if
                    match ty with
                    | FStarC_Custard_Syntax.TAny -> true
                    | uu___2 -> false
                  then
                    let uu___2 =
                      let uu___3 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          b.FStarC_Syntax_Syntax.index in
                      FStarC_SMap.try_find st.lettys uu___3 in
                    match uu___2 with
                    | FStar_Pervasives_Native.Some ty' -> ty'
                    | FStar_Pervasives_Native.None -> ty
                  else ty in
                let uu___2 =
                  let uu___3 = name_of_bv b in
                  FStarC_Custard_Syntax.EVar uu___3 in
                FStarC_Custard_Syntax.mk uu___2 ty1
                  FStarC_Custard_Syntax.E_Pure)
       | FStarC_Syntax_Syntax.Tm_name b ->
           let uu___1 = lifted_ref st b in
           (match uu___1 with
            | FStar_Pervasives_Native.Some e -> e
            | FStar_Pervasives_Native.None ->
                let ty = ty_of_typ st b.FStarC_Syntax_Syntax.sort in
                let ty1 =
                  if
                    match ty with
                    | FStarC_Custard_Syntax.TAny -> true
                    | uu___2 -> false
                  then
                    let uu___2 =
                      let uu___3 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          b.FStarC_Syntax_Syntax.index in
                      FStarC_SMap.try_find st.lettys uu___3 in
                    match uu___2 with
                    | FStar_Pervasives_Native.Some ty' -> ty'
                    | FStar_Pervasives_Native.None -> ty
                  else ty in
                let uu___2 =
                  let uu___3 = name_of_bv b in
                  FStarC_Custard_Syntax.EVar uu___3 in
                FStarC_Custard_Syntax.mk uu___2 ty1
                  FStarC_Custard_Syntax.E_Pure)
       | FStarC_Syntax_Syntax.Tm_uinst (t3, uu___1) -> expr_of_term st t3
       | FStarC_Syntax_Syntax.Tm_fvar fv -> app_of_fv st fv []
       | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
           let uu___2 = FStarC_Syntax_Util.abs_formals t2 in
           (match uu___2 with
            | (bs, body, rc) ->
                let body1 =
                  match rc with
                  | FStar_Pervasives_Native.Some rc1 ->
                      let uu___3 =
                        let uu___4 = tcenv st in env_for_term uu___4 body in
                      FStarC_Custard_Effects.maybe_reify uu___3 body
                        rc1.FStarC_Syntax_Syntax.residual_effect
                  | FStar_Pervasives_Native.None -> body in
                let body2 = expr_of_term st body1 in
                let bs1 =
                  let flags =
                    let uu___3 =
                      let uu___4 = tcenv st in
                      FStarC_Custard_Mono.is_erased_binder uu___4 in
                    FStarC_List.map uu___3 bs in
                  let flags1 =
                    let all_erased =
                      if match flags with | hd::tl -> true | uu___3 -> false
                      then FStarC_List.for_all (fun b -> b) flags
                      else false in
                    let last_erased =
                      match FStarC_List.rev flags with
                      | f::uu___3 -> f
                      | [] -> false in
                    if
                      last_erased &&
                        (all_erased ||
                           (Prims.not
                              (FStarC_Custard_Syntax.is_pure
                                 body2.FStarC_Custard_Syntax.eff)))
                    then
                      match FStarC_List.rev flags with
                      | uu___3::r -> FStarC_List.rev (false :: r)
                      | [] -> flags
                    else flags in
                  drop_flagged flags1 bs in
                let bs2 =
                  FStarC_List.map
                    (fun b ->
                       let uu___3 =
                         name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = tcenv st in
                           FStarC_Custard_Mono.is_erased_binder uu___6 b in
                         if uu___5
                         then FStarC_Custard_Syntax.TUnit
                         else
                           ty_of_typ st
                             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                       {
                         FStarC_Custard_Syntax.b_name = uu___3;
                         FStarC_Custard_Syntax.b_ty = uu___4
                       }) bs1 in
                (match bs2 with
                 | [] -> body2
                 | uu___3 ->
                     let ty =
                       let uu___4 =
                         FStarC_List.fold_right
                           (fun b uu___5 ->
                              match uu___5 with
                              | (ty1, e) ->
                                  ((FStarC_Custard_Syntax.TArrow
                                      ((b.FStarC_Custard_Syntax.b_ty), e,
                                        ty1)), FStarC_Custard_Syntax.E_Pure))
                           bs2
                           ((body2.FStarC_Custard_Syntax.ty),
                             (body2.FStarC_Custard_Syntax.eff)) in
                       FStar_Pervasives_Native.fst uu___4 in
                     FStarC_Custard_Syntax.mk
                       (FStarC_Custard_Syntax.EFun (bs2, body2)) ty
                       FStarC_Custard_Syntax.E_Pure))
       | FStarC_Syntax_Syntax.Tm_app uu___1 ->
           let uu___2 = FStarC_Syntax_Util.head_and_args_full t2 in
           (match uu___2 with
            | (hd, args) ->
                let uu___3 =
                  let uu___4 = FStarC_Syntax_Util.un_uinst hd in
                  uu___4.FStarC_Syntax_Syntax.n in
                (match uu___3 with
                 | FStarC_Syntax_Syntax.Tm_fvar fv -> app_of_fv st fv args
                 | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify
                     (FStar_Pervasives_Native.Some l)) when
                     match args with | hd1::tl -> true | uu___4 -> false ->
                     let e0 =
                       FStar_Pervasives_Native.fst (FStarC_List.hd args) in
                     let e =
                       let uu___4 =
                         let uu___5 = tcenv st in env_for_term uu___5 e0 in
                       FStarC_Custard_Effects.maybe_reify uu___4 e0 l in
                     let uu___4 =
                       let uu___5 = FStarC_TypeChecker_Util.remove_reify e in
                       FStarC_Syntax_Syntax.mk_Tm_app uu___5
                         (FStarC_List.tl args) t2.FStarC_Syntax_Syntax.pos in
                     expr_of_term st uu___4
                 | uu___4 ->
                     let hd_term = hd in
                     let erasable =
                       let uu___5 =
                         let uu___6 = FStarC_Syntax_Subst.compress hd_term in
                         uu___6.FStarC_Syntax_Syntax.n in
                       match uu___5 with
                       | FStarC_Syntax_Syntax.Tm_name bv ->
                           erasable_result st bv.FStarC_Syntax_Syntax.sort
                             args
                       | uu___6 -> false in
                     if erasable
                     then FStarC_Custard_Syntax.unit_expr
                     else
                       (let hd1 = expr_of_term st hd in
                        let sort =
                          let uu___5 =
                            let uu___6 = FStarC_Syntax_Subst.compress hd_term in
                            uu___6.FStarC_Syntax_Syntax.n in
                          match uu___5 with
                          | FStarC_Syntax_Syntax.Tm_name bv ->
                              FStar_Pervasives_Native.Some
                                (bv.FStarC_Syntax_Syntax.sort)
                          | uu___6 -> FStar_Pervasives_Native.None in
                        let flags =
                          match sort with
                          | FStar_Pervasives_Native.Some t3 ->
                              let uu___5 = tcenv st in
                              FStarC_Custard_Mono.erased_binders_unfold
                                uu___5 t3
                          | FStar_Pervasives_Native.None -> [] in
                        let ufs =
                          match sort with
                          | FStar_Pervasives_Native.Some t3 ->
                              let uu___5 =
                                let uu___6 = tcenv st in
                                FStarC_Custard_Mono.unit_binders uu___6 t3 in
                              drop_flagged flags uu___5
                          | FStar_Pervasives_Native.None -> [] in
                        let rec keep ufs1 sp0 =
                          match (ufs1, sp0) with
                          | (true::ufs2, a::sp) ->
                              let uu___5 = keep ufs2 sp in a :: uu___5
                          | (uu___5::ufs2, a::sp) ->
                              let uu___6 =
                                let uu___7 = tcenv st in
                                FStarC_Custard_Mono.is_erased_term uu___7
                                  (FStar_Pervasives_Native.fst a) in
                              if uu___6
                              then keep ufs2 sp
                              else (let uu___7 = keep ufs2 sp in a :: uu___7)
                          | ([], a::sp) ->
                              let uu___5 =
                                let uu___6 = tcenv st in
                                FStarC_Custard_Mono.is_erased_term uu___6
                                  (FStar_Pervasives_Native.fst a) in
                              if uu___5
                              then keep [] sp
                              else (let uu___6 = keep [] sp in a :: uu___6)
                          | (uu___5, []) -> [] in
                        let rec narrow ufs1 sp0 =
                          match (ufs1, sp0) with
                          | (u::ufs', a::sp) ->
                              let uu___5 =
                                if Prims.not u
                                then
                                  let uu___6 = tcenv st in
                                  FStarC_Custard_Mono.is_erased_term uu___6
                                    (FStar_Pervasives_Native.fst a)
                                else false in
                              if uu___5
                              then narrow ufs' sp
                              else
                                (let uu___6 = narrow ufs' sp in u :: uu___6)
                          | uu___5 -> [] in
                        let args0 = drop_flagged flags args in
                        let ufs1 = narrow ufs args0 in
                        let args1 = keep ufs1 args0 in
                        let args2 = value_args st ufs1 args1 in
                        match args2 with
                        | [] -> hd1
                        | uu___5 ->
                            let n = FStarC_List.length args2 in
                            let e =
                              let uu___6 =
                                let uu___7 =
                                  apply_eff st hd1.FStarC_Custard_Syntax.ty n in
                                FStarC_Custard_Syntax.join_eff
                                  hd1.FStarC_Custard_Syntax.eff uu___7 in
                              FStarC_List.fold_left
                                (fun e1 a ->
                                   FStarC_Custard_Syntax.join_eff e1
                                     a.FStarC_Custard_Syntax.eff) uu___6
                                args2 in
                            let uu___6 =
                              apply_result st hd1.FStarC_Custard_Syntax.ty n in
                            FStarC_Custard_Syntax.mk
                              (FStarC_Custard_Syntax.EApp (hd1, args2))
                              uu___6 e)))
       | FStarC_Syntax_Syntax.Tm_let
           { FStarC_Syntax_Syntax.lbs = (true, lbs);
             FStarC_Syntax_Syntax.body1 = body;_}
           -> lift_letrec st lbs body
       | FStarC_Syntax_Syntax.Tm_let
           { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
             FStarC_Syntax_Syntax.body1 = body;_}
           ->
           (match lb.FStarC_Syntax_Syntax.lbname with
            | FStar_Pervasives.Inl bv ->
                let uu___1 = FStarC_Syntax_Subst.open_term_bv bv body in
                (match uu___1 with
                 | (bv1, body1) ->
                     let uu___2 =
                       rename_let_bv t2 bv1 body1
                         lb.FStarC_Syntax_Syntax.lbattrs in
                     (match uu___2 with
                      | (bv2, body2) ->
                          let uu___3 = inlinable_local st lb in
                          if uu___3
                          then
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        FStarC_Syntax_Util.unmeta
                                          lb.FStarC_Syntax_Syntax.lbdef in
                                      (bv2, uu___9) in
                                    FStarC_Syntax_Syntax.NT uu___8 in
                                  [uu___7] in
                                FStarC_Syntax_Subst.subst uu___6 body2 in
                              norm_bounded st "an inlined local function"
                                local_inline_steps uu___5 in
                            expr_of_term st uu___4
                          else
                            (let erased_lb =
                               let uu___4 =
                                 let uu___5 = tcenv st in
                                 FStarC_TypeChecker_Util.must_erase_for_extraction
                                   uu___5 lb.FStarC_Syntax_Syntax.lbtyp in
                               if uu___4
                               then
                                 FStarC_Syntax_Util.is_pure_or_ghost_effect
                                   lb.FStarC_Syntax_Syntax.lbeff
                               else false in
                             let e1 =
                               if erased_lb
                               then FStarC_Custard_Syntax.unit_expr
                               else
                                 expr_of_term st
                                   lb.FStarC_Syntax_Syntax.lbdef in
                             if
                               e1.FStarC_Custard_Syntax.eff =
                                 FStarC_Custard_Syntax.E_Pure
                             then
                               (let uu___5 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int
                                    bv2.FStarC_Syntax_Syntax.index in
                                FStarC_SMap.add st.letdefs uu___5
                                  lb.FStarC_Syntax_Syntax.lbdef)
                             else
                               (let uu___5 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int
                                    bv2.FStarC_Syntax_Syntax.index in
                                FStarC_SMap.add st.effletdefs uu___5 ());
                             (let lty =
                                if erased_lb
                                then e1.FStarC_Custard_Syntax.ty
                                else
                                  (let lty1 =
                                     ty_of_typ st
                                       lb.FStarC_Syntax_Syntax.lbtyp in
                                   if
                                     match lty1 with
                                     | FStarC_Custard_Syntax.TAny -> true
                                     | uu___5 -> false
                                   then e1.FStarC_Custard_Syntax.ty
                                   else lty1) in
                              (let uu___6 =
                                 FStarC_Class_Show.show
                                   FStarC_Class_Show.showable_int
                                   bv2.FStarC_Syntax_Syntax.index in
                               FStarC_SMap.add st.lettys uu___6 lty);
                              (let e2 = expr_of_term st body2 in
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 = name_of_bv bv2 in
                                   (uu___8, lty, e1, e2) in
                                 FStarC_Custard_Syntax.ELet uu___7 in
                               FStarC_Custard_Syntax.mk uu___6
                                 e2.FStarC_Custard_Syntax.ty
                                 (FStarC_Custard_Syntax.join_eff
                                    e1.FStarC_Custard_Syntax.eff
                                    e2.FStarC_Custard_Syntax.eff))))))
            | FStar_Pervasives.Inr uu___1 -> expr_of_term st body)
       | FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = scrutinee;
             FStarC_Syntax_Syntax.ret_opt = uu___1;
             FStarC_Syntax_Syntax.brs = brs;
             FStarC_Syntax_Syntax.rc_opt1 = uu___2;_}
           ->
           let scrut = expr_of_term st scrutinee in
           let brs1 = FStarC_List.map (branch_of_branch st) brs in
           let e =
             FStarC_List.fold_left
               (fun e1 uu___3 ->
                  match uu___3 with
                  | (uu___4, g, b) ->
                      FStarC_Custard_Syntax.join_eff e1
                        (FStarC_Custard_Syntax.join_eff
                           b.FStarC_Custard_Syntax.eff
                           (match g with
                            | FStar_Pervasives_Native.None ->
                                FStarC_Custard_Syntax.E_Pure
                            | FStar_Pervasives_Native.Some g1 ->
                                g1.FStarC_Custard_Syntax.eff)))
               scrut.FStarC_Custard_Syntax.eff brs1 in
           let ty =
             let uu___3 =
               let uu___4 =
                 FStarC_List.map
                   (fun uu___5 ->
                      match uu___5 with
                      | (uu___6, uu___7, b) -> b.FStarC_Custard_Syntax.ty)
                   brs1 in
               FStarC_List.filter
                 (fun t3 ->
                    Prims.not
                      (match t3 with
                       | FStarC_Custard_Syntax.TAny -> true
                       | uu___5 -> false)) uu___4 in
             match uu___3 with
             | [] -> FStarC_Custard_Syntax.TAny
             | t3::ts ->
                 let uu___4 = FStarC_List.for_all (fun u -> u = t3) ts in
                 if uu___4 then t3 else FStarC_Custard_Syntax.TAny in
           FStarC_Custard_Syntax.mk
             (FStarC_Custard_Syntax.EMatch (scrut, brs1)) ty e
       | FStarC_Syntax_Syntax.Tm_ascribed
           { FStarC_Syntax_Syntax.tm = tm; FStarC_Syntax_Syntax.asc = uu___1;
             FStarC_Syntax_Syntax.eff_opt = uu___2;_}
           -> expr_of_term st tm
       | FStarC_Syntax_Syntax.Tm_meta
           { FStarC_Syntax_Syntax.tm2 = tm;
             FStarC_Syntax_Syntax.meta = uu___1;_}
           -> expr_of_term st tm
       | FStarC_Syntax_Syntax.Tm_quoted
           (uu___1,
            {
              FStarC_Syntax_Syntax.qkind = FStarC_Syntax_Syntax.Quote_dynamic;
              FStarC_Syntax_Syntax.antiquotations = uu___2;_})
           ->
           FStarC_Custard_Syntax.mk
             (FStarC_Custard_Syntax.EAbort
                "Custard: cannot evaluate open quotation at runtime")
             FStarC_Custard_Syntax.TAny FStarC_Custard_Syntax.E_Impure
       | FStarC_Syntax_Syntax.Tm_quoted
           (qt,
            { FStarC_Syntax_Syntax.qkind = FStarC_Syntax_Syntax.Quote_static;
              FStarC_Syntax_Syntax.antiquotations = (shift, aqs);_})
           ->
           let repack tv =
             let uu___1 =
               FStarC_Syntax_Util.mk_app
                 (FStarC_Reflection_V2_Constants.refl_constant_term
                    FStarC_Reflection_V2_Constants.fstar_refl_pack_ln)
                 [FStarC_Syntax_Syntax.as_arg tv] in
             expr_of_term st uu___1 in
           let uu___1 = FStarC_Reflection_V2_Builtins.inspect_ln qt in
           (match uu___1 with
            | FStarC_Reflection_V2_Data.Tv_BVar bv ->
                if bv.FStarC_Syntax_Syntax.index < shift
                then
                  let uu___2 =
                    FStarC_Syntax_Embeddings_Base.embed
                      FStarC_Reflection_V2_Embeddings.e_term_view
                      (FStarC_Reflection_V2_Data.Tv_BVar bv)
                      t2.FStarC_Syntax_Syntax.pos
                      FStar_Pervasives_Native.None
                      FStarC_Syntax_Embeddings_Base.id_norm_cb in
                  repack uu___2
                else
                  (let uu___2 =
                     FStarC_Syntax_Syntax.lookup_aq bv (shift, aqs) in
                   expr_of_term st uu___2)
            | tv ->
                let uu___2 =
                  FStarC_Syntax_Embeddings_Base.embed
                    (FStarC_Reflection_V2_Embeddings.e_term_view_aq
                       (shift, aqs)) tv t2.FStarC_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStarC_Syntax_Embeddings_Base.id_norm_cb in
                repack uu___2)
       | FStarC_Syntax_Syntax.Tm_lazy i ->
           let u = FStarC_Syntax_Util.unfold_lazy i in
           let uu___1 =
             let uu___2 = FStarC_Syntax_Subst.compress u in
             uu___2.FStarC_Syntax_Syntax.n in
           (match uu___1 with
            | FStarC_Syntax_Syntax.Tm_lazy uu___2 ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term t2 in
                          truncate_msg uu___8 in
                        Prims.strcat "The term was: " uu___7 in
                      FStarC_Errors_Msg.text uu___6 in
                    [uu___5;
                    FStarC_Errors_Msg.text
                      "This is a value produced by a primitive implementation rather than by the program, so there is no code to generate for it."] in
                  (FStarC_Errors_Msg.text
                     "Custard reached a value with no syntactic representation.")
                    :: uu___4 in
                custard_error st
                  FStarC_Errors_Codes.Error_CustardUnrepresentableValue
                  uu___3
            | uu___2 -> expr_of_term st u)
       | FStarC_Syntax_Syntax.Tm_type uu___1 ->
           FStarC_Custard_Syntax.unit_expr
       | uu___1 -> FStarC_Custard_Syntax.unit_expr)
and lifted_ref (st : state) (b : FStarC_Syntax_Syntax.bv) :
  FStarC_Custard_Syntax.expr FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = name_of_bv b in FStarC_SMap.try_find st.lifted uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (nm, tyargs, caps, ty, uu___1) ->
      let hd =
        FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EQual (nm, tyargs))
          ty FStarC_Custard_Syntax.E_Pure in
      (match caps with
       | [] -> FStar_Pervasives_Native.Some hd
       | uu___2 ->
           let args =
             FStarC_List.map
               (fun b1 ->
                  FStarC_Custard_Syntax.mk
                    (FStarC_Custard_Syntax.EVar
                       (b1.FStarC_Custard_Syntax.b_name))
                    b1.FStarC_Custard_Syntax.b_ty
                    FStarC_Custard_Syntax.E_Pure) caps in
           let n = FStarC_List.length args in
           let uu___3 =
             let uu___4 = apply_result st ty n in
             FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EApp (hd, args))
               uu___4 FStarC_Custard_Syntax.E_Pure in
           FStar_Pervasives_Native.Some uu___3)
and is_type_bv (st : state) (b : FStarC_Syntax_Syntax.bv) : Prims.bool=
  let uu___ = tcenv st in
  FStarC_Custard_Mono.is_type_binder uu___ (FStarC_Syntax_Syntax.mk_binder b)
and lift_letrec (st : state)
  (lbs : FStarC_Syntax_Syntax.letbinding Prims.list)
  (body : FStarC_Syntax_Syntax.term) : FStarC_Custard_Syntax.expr=
  let uu___ = FStarC_Syntax_Subst.open_let_rec lbs body in
  match uu___ with
  | (lbs1, body1) ->
      let recbvs =
        FStarC_List.collect
          (fun lb ->
             match lb.FStarC_Syntax_Syntax.lbname with
             | FStar_Pervasives.Inl bv -> [bv]
             | FStar_Pervasives.Inr uu___1 -> []) lbs1 in
      if (FStarC_List.length recbvs) <> (FStarC_List.length lbs1)
      then expr_of_term st body1
      else
        (let free =
           FStarC_List.collect
             (fun lb ->
                let uu___1 =
                  FStarC_Syntax_Free.names lb.FStarC_Syntax_Syntax.lbdef in
                FStarC_Class_Setlike.elems
                  (FStarC_FlatSet.setlike_flat_set
                     FStarC_Syntax_Syntax.ord_bv) uu___1) lbs1 in
         let free1 =
           FStarC_List.filter
             (fun v ->
                let uu___1 =
                  FStarC_List.existsb
                    (fun r -> FStarC_Syntax_Syntax.bv_eq r v) recbvs in
                Prims.not uu___1) free in
         let rec dedup1 l =
           match l with
           | [] -> []
           | x::xs ->
               let uu___1 =
                 let uu___2 =
                   FStarC_List.filter
                     (fun y -> Prims.not (FStarC_Syntax_Syntax.bv_eq x y)) xs in
                 dedup1 uu___2 in
               x :: uu___1 in
         let rec expand fuel l =
           if fuel <= Prims.int_zero
           then l
           else
             (let hit = FStarC_Effect.alloc false in
              let l1 =
                FStarC_List.collect
                  (fun v ->
                     let uu___1 =
                       let uu___2 = name_of_bv v in
                       FStarC_SMap.try_find st.lifted uu___2 in
                     match uu___1 with
                     | FStar_Pervasives_Native.Some
                         (uu___2, uu___3, uu___4, uu___5, vs) ->
                         (FStarC_Effect.op_Colon_Equals hit true; vs)
                     | FStar_Pervasives_Native.None -> [v]) l in
              let uu___1 = FStarC_Effect.op_Bang hit in
              if uu___1 then expand (fuel - Prims.int_one) l1 else l1) in
         let free2 = expand (Prims.of_int 100) free1 in
         let free3 =
           let uu___1 = dedup1 free2 in
           FStarC_List.sortWith
             (fun x y ->
                x.FStarC_Syntax_Syntax.index - y.FStarC_Syntax_Syntax.index)
             uu___1 in
         let uu___1 = FStarC_List.partition (is_type_bv st) free3 in
         match uu___1 with
         | (tyvars, valvars) ->
             let valvars1 =
               FStarC_List.filter
                 (fun v ->
                    let uu___2 =
                      let uu___3 = tcenv st in
                      FStarC_Custard_Mono.is_erased_binder uu___3
                        (FStarC_Syntax_Syntax.mk_binder v) in
                    Prims.not uu___2) valvars in
             let typars =
               let uu___2 =
                 FStarC_List.filter
                   (fun v ->
                      let uu___3 = tcenv st in
                      FStarC_Custard_Mono.is_type_param uu___3
                        (FStarC_Syntax_Syntax.mk_binder v)) tyvars in
               FStarC_List.map name_of_bv uu___2 in
             let tyargs =
               FStarC_List.map (fun v -> FStarC_Custard_Syntax.TVar v) typars in
             let caps =
               FStarC_List.map
                 (fun v ->
                    let uu___2 = name_of_bv v in
                    let uu___3 = ty_of_typ st v.FStarC_Syntax_Syntax.sort in
                    {
                      FStarC_Custard_Syntax.b_name = uu___2;
                      FStarC_Custard_Syntax.b_ty = uu___3
                    }) valvars1 in
             let entries =
               FStarC_List.map
                 (fun lb ->
                    let bv =
                      match lb.FStarC_Syntax_Syntax.lbname with
                      | FStar_Pervasives.Inl v -> v in
                    let base =
                      let uu___2 =
                        let uu___3 = FStarC_Effect.op_Bang st.cur in
                        uu___3.FStarC_Custard_Syntax.id in
                      Prims.strcat uu___2
                        (Prims.strcat "__"
                           (FStarC_Ident.string_of_id
                              bv.FStarC_Syntax_Syntax.ppname)) in
                    let ns =
                      let uu___2 = FStarC_Effect.op_Bang st.cur in
                      uu___2.FStarC_Custard_Syntax.ns in
                    let esp =
                      let uu___2 = FStarC_Effect.op_Bang st.cur in
                      uu___2.FStarC_Custard_Syntax.spec in
                    let ckey =
                      Prims.strcat base
                        (match esp with
                         | FStar_Pervasives_Native.None -> ""
                         | FStar_Pervasives_Native.Some s ->
                             Prims.strcat "@" s) in
                    let n =
                      let uu___2 = FStarC_SMap.try_find st.counts ckey in
                      match uu___2 with
                      | FStar_Pervasives_Native.None -> Prims.int_zero
                      | FStar_Pervasives_Native.Some n1 -> n1 in
                    FStarC_SMap.add st.counts ckey (n + Prims.int_one);
                    (let nm =
                       let uu___3 =
                         match (esp, n) with
                         | (FStar_Pervasives_Native.None, uu___4) when
                             uu___4 = Prims.int_zero ->
                             FStar_Pervasives_Native.None
                         | (FStar_Pervasives_Native.None, n1) ->
                             let uu___4 =
                               FStarC_Class_Show.show
                                 FStarC_Class_Show.showable_int n1 in
                             FStar_Pervasives_Native.Some uu___4
                         | (FStar_Pervasives_Native.Some s, uu___4) when
                             uu___4 = Prims.int_zero ->
                             FStar_Pervasives_Native.Some s
                         | (FStar_Pervasives_Native.Some s, n1) ->
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   FStarC_Class_Show.show
                                     FStarC_Class_Show.showable_int n1 in
                                 Prims.strcat "_" uu___6 in
                               Prims.strcat s uu___5 in
                             FStar_Pervasives_Native.Some uu___4 in
                       {
                         FStarC_Custard_Syntax.ns = ns;
                         FStarC_Custard_Syntax.id = base;
                         FStarC_Custard_Syntax.spec = uu___3
                       } in
                     let uu___3 =
                       FStarC_Syntax_Util.abs_formals
                         lb.FStarC_Syntax_Syntax.lbdef in
                     match uu___3 with
                     | (xs, def_body, rc) ->
                         let def_body1 =
                           let ambient uu___4 =
                             let uu___5 =
                               FStarC_Syntax_Util.arrow_formals_comp
                                 lb.FStarC_Syntax_Syntax.lbtyp in
                             match uu___5 with
                             | (uu___6, c) ->
                                 FStarC_Syntax_Util.comp_effect_name c in
                           let eff_name =
                             match rc with
                             | FStar_Pervasives_Native.Some rc1 ->
                                 rc1.FStarC_Syntax_Syntax.residual_effect
                             | FStar_Pervasives_Native.None -> ambient () in
                           let uu___4 =
                             let uu___5 = tcenv st in
                             env_for_term uu___5 def_body in
                           FStarC_Custard_Effects.maybe_reify uu___4 def_body
                             eff_name in
                         let uu___4 =
                           local_result st lb.FStarC_Syntax_Syntax.lbtyp xs in
                         (match uu___4 with
                          | (ret, eff) ->
                              let uu___5 =
                                FStarC_List.partition
                                  (fun b ->
                                     is_type_bv st
                                       b.FStarC_Syntax_Syntax.binder_bv) xs in
                              (match uu___5 with
                               | (tybs, valbs) ->
                                   let valbs1 =
                                     FStarC_List.filter
                                       (fun b ->
                                          let uu___6 =
                                            let uu___7 = tcenv st in
                                            FStarC_Custard_Mono.is_erased_binder
                                              uu___7 b in
                                          Prims.not uu___6) valbs in
                                   let own_typars =
                                     FStarC_List.map
                                       (fun b ->
                                          name_of_bv
                                            b.FStarC_Syntax_Syntax.binder_bv)
                                       tybs in
                                   let arg_binders =
                                     FStarC_List.map
                                       (fun b ->
                                          let uu___6 =
                                            name_of_bv
                                              b.FStarC_Syntax_Syntax.binder_bv in
                                          let uu___7 =
                                            ty_of_typ st
                                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                          {
                                            FStarC_Custard_Syntax.b_name =
                                              uu___6;
                                            FStarC_Custard_Syntax.b_ty =
                                              uu___7
                                          }) valbs1 in
                                   let binders =
                                     FStarC_List.op_At caps arg_binders in
                                   let ty =
                                     let uu___6 =
                                       FStarC_List.fold_right
                                         (fun b uu___7 ->
                                            match uu___7 with
                                            | (t, e) ->
                                                ((FStarC_Custard_Syntax.TArrow
                                                    ((b.FStarC_Custard_Syntax.b_ty),
                                                      e, t)),
                                                  FStarC_Custard_Syntax.E_Pure))
                                         binders (ret, eff) in
                                     FStar_Pervasives_Native.fst uu___6 in
                                   ((let uu___7 = name_of_bv bv in
                                     FStarC_SMap.add st.lifted uu___7
                                       (nm, tyargs, caps, ty, free3));
                                    (nm, binders, ret, eff, own_typars,
                                      def_body1)))))) lbs1 in
             let local_key nm =
               let uu___2 = FStarC_Custard_Syntax.mangled_name nm in
               Prims.strcat "<local>" uu___2 in
             (FStarC_List.iter
                (fun uu___3 ->
                   match uu___3 with
                   | (nm, binders, ret, eff, own_typars, uu___4) ->
                       let uu___5 = local_key nm in
                       FStarC_SMap.add st.emitted uu___5
                         (FStarC_Custard_Syntax.DLet
                            {
                              FStarC_Custard_Syntax.dl_name = nm;
                              FStarC_Custard_Syntax.dl_typars =
                                (FStarC_List.op_At typars own_typars);
                              FStarC_Custard_Syntax.dl_binders = binders;
                              FStarC_Custard_Syntax.dl_ret = ret;
                              FStarC_Custard_Syntax.dl_eff = eff;
                              FStarC_Custard_Syntax.dl_body =
                                (FStarC_Custard_Syntax.mk
                                   (FStarC_Custard_Syntax.EAbort
                                      "Custard: provisional body") ret eff);
                              FStarC_Custard_Syntax.dl_flags = []
                            })) entries;
              FStarC_List.iter
                (fun uu___4 ->
                   match uu___4 with
                   | (nm, binders, ret, eff, own_typars, def_body) ->
                       let saved_cur = FStarC_Effect.op_Bang st.cur in
                       let saved_cur_lid = FStarC_Effect.op_Bang st.cur_lid in
                       (FStarC_Effect.op_Colon_Equals st.cur nm;
                        FStarC_Effect.op_Colon_Equals st.cur_lid
                          FStar_Pervasives_Native.None;
                        (let d =
                           let uu___7 =
                             let uu___8 = expr_of_term st def_body in
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_List.map
                                     (fun uu___12 ->
                                        match uu___12 with
                                        | (nm1, uu___13, uu___14, uu___15,
                                           uu___16, uu___17) -> nm1) entries in
                                 FStarC_Custard_Syntax.Rec uu___11 in
                               [uu___10] in
                             {
                               FStarC_Custard_Syntax.dl_name = nm;
                               FStarC_Custard_Syntax.dl_typars =
                                 (FStarC_List.op_At typars own_typars);
                               FStarC_Custard_Syntax.dl_binders = binders;
                               FStarC_Custard_Syntax.dl_ret = ret;
                               FStarC_Custard_Syntax.dl_eff = eff;
                               FStarC_Custard_Syntax.dl_body = uu___8;
                               FStarC_Custard_Syntax.dl_flags = uu___9
                             } in
                           FStarC_Custard_Syntax.DLet uu___7 in
                         let key = local_key nm in
                         FStarC_Effect.op_Colon_Equals st.cur saved_cur;
                         FStarC_Effect.op_Colon_Equals st.cur_lid
                           saved_cur_lid;
                         FStarC_SMap.add st.emitted key d;
                         (let uu___10 =
                            let uu___11 = FStarC_Effect.op_Bang st.order in
                            key :: uu___11 in
                          FStarC_Effect.op_Colon_Equals st.order uu___10))))
                entries;
              expr_of_term st body1))
and local_result (st : state) (ty : FStarC_Syntax_Syntax.typ)
  (xs : FStarC_Syntax_Syntax.binders) :
  (FStarC_Custard_Syntax.cty * FStarC_Custard_Syntax.eff)=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp ty in
  match uu___ with
  | (bs, c) ->
      let rec realign bs1 xs1 =
        match (bs1, xs1) with
        | (b::bs2, x::xs2) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_Syntax_Syntax.bv_to_name
                    x.FStarC_Syntax_Syntax.binder_bv in
                ((b.FStarC_Syntax_Syntax.binder_bv), uu___3) in
              FStarC_Syntax_Syntax.NT uu___2 in
            let uu___2 = realign bs2 xs2 in uu___1 :: uu___2
        | uu___1 -> [] in
      let c1 =
        let uu___1 = realign bs xs in FStarC_Syntax_Subst.subst_comp uu___1 c in
      let rec peel n e t =
        if n <= Prims.int_zero
        then (e, t)
        else
          (match t with
           | FStarC_Custard_Syntax.TArrow (uu___1, e', r) ->
               peel (n - Prims.int_one) e' r
           | uu___1 -> (e, t)) in
      let n_extra = (FStarC_List.length xs) - (FStarC_List.length bs) in
      let uu___1 =
        let uu___2 =
          let uu___3 = tcenv st in
          FStarC_Custard_Effects.is_erasable uu___3 c1 in
        if uu___2
        then (FStarC_Custard_Syntax.E_Ghost, FStarC_Custard_Syntax.TUnit)
        else
          (let uu___3 =
             let uu___4 = tcenv st in
             FStarC_Custard_Effects.is_reifiable uu___4
               (FStarC_Syntax_Util.comp_effect_name c1) in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 let uu___6 = let uu___7 = tcenv st in env_for_comp uu___7 c1 in
                 FStarC_Custard_Effects.reify_comp uu___6 c1 in
               ty_of_typ st uu___5 in
             peel n_extra FStarC_Custard_Syntax.E_Pure uu___4
           else
             (let uu___4 = eff_of_comp st c1 in
              let uu___5 =
                let uu___6 =
                  let uu___7 = tcenv st in
                  FStarC_Custard_Effects.result_typ uu___7 c1 in
                ty_of_typ st uu___6 in
              peel n_extra uu___4 uu___5)) in
      (match uu___1 with | (eff, ret) -> (ret, eff))
and keep_flagged :
  'a . Prims.bool Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun flags xs ->
    match (flags, xs) with
    | (uu___, []) -> []
    | ([], uu___) -> []
    | (f::flags1, x::xs1) ->
        let rest = keep_flagged flags1 xs1 in if f then x :: rest else rest
and drop_flagged :
  'a . Prims.bool Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun flags xs ->
    match (flags, xs) with
    | (uu___, []) -> []
    | ([], xs1) -> xs1
    | (f::flags1, x::xs1) ->
        let rest = drop_flagged flags1 xs1 in if f then rest else x :: rest
and app_of_fv (st : state) (fv : FStarC_Syntax_Syntax.fv)
  (args : FStarC_Syntax_Syntax.args) : FStarC_Custard_Syntax.expr=
  let l = FStarC_Syntax_Syntax.lid_of_fv fv in
  let uu___ = FStarC_Custard_Builtins.lookup_rule l in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_prim (n, f))
      -> prim_app st l n f args
  | uu___1 ->
      let uu___2 =
        let uu___3 = lookup_lid_typ st l in erasable_app st uu___3 args in
      if uu___2
      then FStarC_Custard_Syntax.unit_expr
      else app_of_fv' st fv args
and erasable_app (st : state)
  (lookup :
    ((FStarC_Syntax_Syntax.universes * FStarC_Syntax_Syntax.typ) *
      FStarC_Range_Type.range) FStar_Pervasives_Native.option)
  (args : FStarC_Syntax_Syntax.args) : Prims.bool=
  match lookup with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some ((uu___, ty), uu___1) ->
      erasable_result st ty args
and erasable_result (st : state) (ty : FStarC_Syntax_Syntax.typ)
  (args : FStarC_Syntax_Syntax.args) : Prims.bool=
  FStarC_Custard_Prof.timed "erasable"
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Util.arrow_formals_comp ty in
       match uu___1 with
       | (bs, c) ->
           let uu___2 =
             if (FStarC_List.length bs) = (FStarC_List.length args)
             then FStarC_Syntax_Util.is_pure_or_ghost_comp c
             else false in
           if uu___2
           then
             let subst =
               FStarC_List.map2
                 (fun b uu___3 ->
                    match uu___3 with
                    | (a, uu___4) ->
                        FStarC_Syntax_Syntax.NT
                          ((b.FStarC_Syntax_Syntax.binder_bv), a)) bs args in
             let uu___3 = tcenv st in
             let uu___4 =
               FStarC_Syntax_Subst.subst subst
                 (FStarC_Syntax_Util.comp_result c) in
             FStarC_TypeChecker_Util.must_erase_for_extraction uu___3 uu___4
           else false)
and prim_app (st : state) (l : FStarC_Ident.lident) (n : Prims.int)
  (f :
    FStarC_Custard_Syntax.cty Prims.list ->
      FStarC_Custard_Syntax.expr Prims.list -> FStarC_Custard_Syntax.expr)
  (args : FStarC_Syntax_Syntax.args) : FStarC_Custard_Syntax.expr=
  let decl_ty =
    let uu___ = lookup_lid_typ st l in
    match uu___ with
    | FStar_Pervasives_Native.Some ((uu___1, ty), uu___2) ->
        FStar_Pervasives_Native.Some ty
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let flags =
    match decl_ty with
    | FStar_Pervasives_Native.Some ty ->
        let uu___ = tcenv st in
        FStarC_Custard_Mono.erased_binders_unfold uu___ ty
    | FStar_Pervasives_Native.None -> [] in
  let tyargs =
    match decl_ty with
    | FStar_Pervasives_Native.Some ty ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = tcenv st in
              FStarC_Custard_Mono.type_params uu___3 ty in
            keep_flagged uu___2 args in
          FStarC_List.map FStar_Pervasives_Native.fst uu___1 in
        FStarC_List.map (ty_of_typ st) uu___
    | FStar_Pervasives_Native.None -> [] in
  let args1 =
    if
      match decl_ty with
      | FStar_Pervasives_Native.None -> true
      | uu___ -> false
    then
      FStarC_List.filter
        (fun uu___ ->
           match uu___ with
           | (a, uu___1) ->
               let uu___2 =
                 let uu___3 = tcenv st in
                 FStarC_Custard_Mono.is_type_term uu___3 a in
               Prims.not uu___2) args
    else drop_flagged flags args in
  let unit_kept =
    if
      match decl_ty with
      | FStar_Pervasives_Native.None -> true
      | uu___ -> false
    then []
    else
      (let uu___ = binder_flags st "u:" l FStarC_Custard_Mono.unit_binders in
       drop_flagged flags uu___) in
  let args2 =
    let uu___ = FStarC_Custard_Builtins.normalizes_arguments l in
    if uu___
    then
      FStarC_List.map
        (fun uu___1 ->
           match uu___1 with
           | (a, q) ->
               let uu___2 =
                 norm_bounded st
                   (Prims.strcat "the compile-time argument of "
                      (FStarC_Ident.string_of_lid l)) compile_time_steps a in
               (uu___2, q)) args1
    else args1 in
  let args3 =
    let uu___ = FStarC_List.map FStar_Pervasives_Native.fst args2 in
    FStarC_List.map (expr_of_term st) uu___ in
  let args4 =
    FStarC_List.map
      (fun e ->
         let uu___ = head_ty st e.FStarC_Custard_Syntax.ty (Prims.of_int 10) in
         {
           FStarC_Custard_Syntax.e = (e.FStarC_Custard_Syntax.e);
           FStarC_Custard_Syntax.ty = uu___;
           FStarC_Custard_Syntax.eff = (e.FStarC_Custard_Syntax.eff)
         }) args3 in
  (match decl_ty with
   | FStar_Pervasives_Native.Some ty ->
       let retained =
         let uu___1 =
           let uu___2 =
             let uu___3 = tcenv st in
             FStarC_Custard_Mono.erased_binders_unfold uu___3 ty in
           FStarC_List.filter (fun b -> Prims.not b) uu___2 in
         FStarC_List.length uu___1 in
       if n > retained
       then
         let uu___1 =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       FStarC_Class_Show.show FStarC_Class_Show.showable_int
                         n in
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           FStarC_Class_Show.show
                             FStarC_Class_Show.showable_nat retained in
                         Prims.strcat uu___10 " binder(s) after erasure." in
                       Prims.strcat ", but the declaration retains only "
                         uu___9 in
                     Prims.strcat uu___7 uu___8 in
                   Prims.strcat " declares arity " uu___6 in
                 Prims.strcat (FStarC_Ident.string_of_lid l) uu___5 in
               Prims.strcat "The rule for " uu___4 in
             FStar_Pprint.doc_of_string uu___3 in
           [uu___2;
           FStar_Pprint.doc_of_string
             "No use site can supply that many arguments, so every use is eta-expanded and the rule's result is a lambda that nothing applies.  Any effect the rule performs still happens, so the output may contain the definitions it produced and no call to them."] in
         custard_warning st FStarC_Errors_Codes.Warning_CustardRuleArity
           uu___1
       else ()
   | FStar_Pervasives_Native.None -> ());
  (let uu___1 =
     if (FStarC_List.length args4) <= n
     then (args4, [])
     else FStarC_List.splitAt n args4 in
   match uu___1 with
   | (given, extra) ->
       let extra1 =
         let uu___2 =
           let uu___3 = FStarC_List.mapi (fun i e -> ((i + n), e)) extra in
           FStarC_List.filter
             (fun uu___4 ->
                match uu___4 with
                | (j, uu___5) ->
                    Prims.not
                      ((j < (FStarC_List.length unit_kept)) &&
                         (FStarC_List.nth unit_kept j))) uu___3 in
         FStarC_List.map FStar_Pervasives_Native.snd uu___2 in
       let missing = n - (FStarC_List.length given) in
       if missing > Prims.int_zero
       then
         let sorts =
           match decl_ty with
           | FStar_Pervasives_Native.Some ty ->
               let uu___2 = tcenv st in
               FStarC_Custard_Mono.retained_sorts uu___2 ty
           | FStar_Pervasives_Native.None -> [] in
         let bnames =
           match decl_ty with
           | FStar_Pervasives_Native.Some ty ->
               let uu___2 = tcenv st in
               FStarC_Custard_Mono.retained_names uu___2 ty
           | FStar_Pervasives_Native.None -> [] in
         let nth_sort i =
           let j = (FStarC_List.length given) + i in
           if j < (FStarC_List.length sorts)
           then ty_of_typ st (FStarC_List.nth sorts j)
           else FStarC_Custard_Syntax.TAny in
         let nth_name i =
           let j = (FStarC_List.length given) + i in
           if j < (FStarC_List.length bnames)
           then
             let n1 = FStarC_List.nth bnames j in
             (if n1 = "" then "eta" else n1)
           else "eta" in
         let bs =
           let uu___2 = repeat_unit missing in
           FStarC_List.mapi
             (fun i uu___3 ->
                let uu___4 =
                  let uu___5 = nth_name i in
                  let uu___6 = FStarC_GenSym.next_id () in
                  FStarC_Custard_Syntax.uniq uu___5 uu___6 in
                let uu___5 = nth_sort i in
                {
                  FStarC_Custard_Syntax.b_name = uu___4;
                  FStarC_Custard_Syntax.b_ty = uu___5
                }) uu___2 in
         let vs =
           FStarC_List.map
             (fun b ->
                FStarC_Custard_Syntax.mk
                  (FStarC_Custard_Syntax.EVar
                     (b.FStarC_Custard_Syntax.b_name))
                  b.FStarC_Custard_Syntax.b_ty FStarC_Custard_Syntax.E_Pure)
             bs in
         let body = f tyargs (FStarC_List.op_At given vs) in
         let uu___2 =
           FStarC_List.fold_right
             (fun b t ->
                FStarC_Custard_Syntax.TArrow
                  ((b.FStarC_Custard_Syntax.b_ty),
                    FStarC_Custard_Syntax.E_Pure, t)) bs
             body.FStarC_Custard_Syntax.ty in
         FStarC_Custard_Syntax.mk (FStarC_Custard_Syntax.EFun (bs, body))
           uu___2 FStarC_Custard_Syntax.E_Pure
       else
         (let e = f tyargs given in
          match extra1 with
          | [] -> e
          | uu___2 ->
              ((let uu___4 =
                  head_ty st e.FStarC_Custard_Syntax.ty (Prims.of_int 10) in
                match uu___4 with
                | FStarC_Custard_Syntax.TArrow uu___5 -> ()
                | rty ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int n in
                                let uu___12 =
                                  let uu___13 =
                                    let uu___14 =
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_nat
                                        (FStarC_List.length args4) in
                                    let uu___15 =
                                      let uu___16 =
                                        let uu___17 =
                                          FStarC_Class_Show.show
                                            FStarC_Custard_Syntax.showable_cty
                                            rty in
                                        Prims.strcat uu___17 "." in
                                      Prims.strcat
                                        " argument(s), and the rule's result is not a function: it has type "
                                        uu___16 in
                                    Prims.strcat uu___14 uu___15 in
                                  Prims.strcat ", but the use site supplies "
                                    uu___13 in
                                Prims.strcat uu___11 uu___12 in
                              Prims.strcat " declares arity " uu___10 in
                            Prims.strcat (FStarC_Ident.string_of_lid l)
                              uu___9 in
                          Prims.strcat "The rule for " uu___8 in
                        FStar_Pprint.doc_of_string uu___7 in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_nat
                                  (FStarC_List.length extra1) in
                              Prims.strcat uu___11
                                " left-over argument(s) are applied to that result, which is not something the target can run -- it reaches C as a call through a non-function and is reported there, about generated code." in
                            Prims.strcat "The " uu___10 in
                          FStar_Pprint.doc_of_string uu___9 in
                        [uu___8;
                        FStar_Pprint.doc_of_string
                          "A rule's arity counts every argument the declaration retains, including the trailing unit applications of a Pulse [fn], not only the ones the rule reads."] in
                      uu___6 :: uu___7 in
                    custard_warning st
                      FStarC_Errors_Codes.Warning_CustardRuleArity uu___5);
               (let uu___4 =
                  apply_result st e.FStarC_Custard_Syntax.ty
                    (FStarC_List.length extra1) in
                let uu___5 =
                  let uu___6 =
                    apply_eff st e.FStarC_Custard_Syntax.ty
                      (FStarC_List.length extra1) in
                  FStarC_List.fold_left
                    (fun x a ->
                       FStarC_Custard_Syntax.join_eff x
                         a.FStarC_Custard_Syntax.eff) uu___6 extra1 in
                FStarC_Custard_Syntax.mk
                  (FStarC_Custard_Syntax.EApp (e, extra1)) uu___4 uu___5))))
and binder_flags (st : state) (tag : Prims.string) (l : FStarC_Ident.lident)
  (f :
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ -> Prims.bool Prims.list)
  : Prims.bool Prims.list=
  let key = Prims.strcat tag (FStarC_Ident.string_of_lid l) in
  let uu___ = FStarC_SMap.try_find st.bflags key in
  match uu___ with
  | FStar_Pervasives_Native.Some fs -> fs
  | FStar_Pervasives_Native.None ->
      let uu___1 = lookup_lid_typ st l in
      (match uu___1 with
       | FStar_Pervasives_Native.None -> []
       | FStar_Pervasives_Native.Some ((uu___2, ty), uu___3) ->
           let fs = let uu___4 = tcenv st in f uu___4 ty in
           (FStarC_SMap.add st.bflags key fs; fs))
and ctor_dropped_flags (st : state) (l : FStarC_Ident.lident) :
  Prims.bool Prims.list=
  let n_params =
    let uu___ =
      let uu___1 = tcenv st in FStarC_TypeChecker_Env.lookup_sigelt uu___1 l in
    match uu___ with
    | FStar_Pervasives_Native.Some
        {
          FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
            { FStarC_Syntax_Syntax.lid1 = uu___1;
              FStarC_Syntax_Syntax.us1 = uu___2;
              FStarC_Syntax_Syntax.t1 = uu___3;
              FStarC_Syntax_Syntax.ty_lid = uu___4;
              FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
              FStarC_Syntax_Syntax.mutuals1 = uu___5;
              FStarC_Syntax_Syntax.injective_type_params1 = uu___6;
              FStarC_Syntax_Syntax.proj_disc_lids = uu___7;_};
          FStarC_Syntax_Syntax.sigrng = uu___8;
          FStarC_Syntax_Syntax.sigquals = uu___9;
          FStarC_Syntax_Syntax.sigmeta = uu___10;
          FStarC_Syntax_Syntax.sigattrs = uu___11;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
          FStarC_Syntax_Syntax.sigopts = uu___13;_}
        -> num_ty_params
    | uu___1 -> Prims.int_zero in
  let uu___ = binder_flags st "e:" l FStarC_Custard_Mono.erased_binders in
  FStarC_List.mapi (fun i erased -> erased || (i < n_params)) uu___
and repeat_unit (n : Prims.int) : unit Prims.list=
  if n <= Prims.int_zero
  then []
  else (let uu___ = repeat_unit (n - Prims.int_one) in () :: uu___)
and app_of_fv' (st : state) (fv : FStarC_Syntax_Syntax.fv)
  (args : FStarC_Syntax_Syntax.args) : FStarC_Custard_Syntax.expr=
  FStarC_Custard_Prof.timed "app_of_fv"
    (fun uu___ ->
       let l = FStarC_Syntax_Syntax.lid_of_fv fv in
       ensure_lid_available st l;
       (let uu___2 = is_data_ctor fv in
        if uu___2
        then
          let nm =
            request st
              {
                sk_lid = l;
                sk_args = [];
                sk_subst = [];
                sk_holes = Prims.int_zero
              } in
          let flags = ctor_dropped_flags st l in
          let ufs = binder_flags st "u:" l FStarC_Custard_Mono.unit_binders in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = drop_flagged flags ufs in
                let uu___7 = drop_flagged flags args in
                value_args st uu___6 uu___7 in
              (nm, uu___5) in
            FStarC_Custard_Syntax.ECtor uu___4 in
          let uu___4 = ctor_result_ty st l args in
          FStarC_Custard_Syntax.mk uu___3 uu___4 FStarC_Custard_Syntax.E_Pure
        else
          (let cs = binder_classes st l in
           let uu___3 = split_mono_args st l cs args in
           match uu___3 with
           | (margs, msubst, rest, holes) ->
               let key =
                 {
                   sk_lid = l;
                   sk_args = margs;
                   sk_subst = msubst;
                   sk_holes = (FStarC_List.length holes)
                 } in
               let nm = request st key in
               let tyargs = call_type_args st l cs args in
               let hd_ty =
                 let uu___4 = string_of_key key in
                 callee_sig st uu___4 tyargs in
               let hd =
                 FStarC_Custard_Syntax.mk
                   (FStarC_Custard_Syntax.EQual (nm, tyargs)) hd_ty
                   FStarC_Custard_Syntax.E_Pure in
               let rest1 =
                 let uu___4 = call_unit_flags st l cs args in
                 value_args st uu___4 rest in
               let hargs =
                 FStarC_List.map
                   (fun v ->
                      let uu___4 = FStarC_Syntax_Syntax.bv_to_name v in
                      expr_of_term st uu___4) holes in
               let rest2 = FStarC_List.op_At hargs rest1 in
               (match rest2 with
                | [] -> hd
                | uu___4 ->
                    let e =
                      let uu___5 =
                        let uu___6 = string_of_key key in
                        callee_eff st uu___6 (FStarC_List.length rest2) in
                      FStarC_List.fold_left
                        (fun e1 a ->
                           FStarC_Custard_Syntax.join_eff e1
                             a.FStarC_Custard_Syntax.eff) uu___5 rest2 in
                    let uu___5 =
                      apply_result st hd_ty (FStarC_List.length rest2) in
                    FStarC_Custard_Syntax.mk
                      (FStarC_Custard_Syntax.EApp (hd, rest2)) uu___5 e))))
and ctor_result_ty (st : state) (l : FStarC_Ident.lident)
  (spine : FStarC_Syntax_Syntax.args) : FStarC_Custard_Syntax.cty=
  let uu___ = lookup_lid_typ st l in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStarC_Custard_Syntax.TAny
  | FStar_Pervasives_Native.Some ((uu___1, ty), uu___2) ->
      let uu___3 = FStarC_Syntax_Util.arrow_formals_comp ty in
      (match uu___3 with
       | (bs, c) ->
           let rec go bs1 sp acc =
             match (bs1, sp) with
             | (b::bs2, (a, uu___4)::sp1) ->
                 go bs2 sp1
                   ((FStarC_Syntax_Syntax.NT
                       ((b.FStarC_Syntax_Syntax.binder_bv), a)) :: acc)
             | uu___4 -> acc in
           let uu___4 =
             let uu___5 = go bs spine [] in
             FStarC_Syntax_Subst.subst uu___5
               (FStarC_Syntax_Util.comp_result c) in
           ty_of_typ st uu___4)
and value_args (st : state) (ufs : Prims.bool Prims.list)
  (spine : FStarC_Syntax_Syntax.args) :
  FStarC_Custard_Syntax.expr Prims.list=
  match (ufs, spine) with
  | (true::ufs1, uu___::sp) ->
      let uu___1 = value_args st ufs1 sp in FStarC_Custard_Syntax.unit_expr
        :: uu___1
  | (uu___::ufs1, (a, uu___1)::sp) ->
      let uu___2 = expr_of_term st a in
      let uu___3 = value_args st ufs1 sp in uu___2 :: uu___3
  | ([], (a, uu___)::sp) ->
      let uu___1 = expr_of_term st a in
      let uu___2 = value_args st [] sp in uu___1 :: uu___2
  | (uu___, []) -> []
and call_unit_flags (st : state) (l : FStarC_Ident.lident)
  (cs : FStarC_Custard_Mono.bclass Prims.list)
  (spine : FStarC_Syntax_Syntax.args) : Prims.bool Prims.list=
  FStarC_Custard_Prof.timed "call_unit_flags"
    (fun uu___ ->
       let ub = binder_flags st "u:" l FStarC_Custard_Mono.unit_binders in
       let rec go cs1 uf sp =
         match (cs1, sp) with
         | ([], uu___1) -> []
         | (c::cs2, uu___1::sp1) ->
             let uu___2 =
               match uf with | u::uf1 -> (u, uf1) | [] -> (false, []) in
             (match uu___2 with
              | (u, uf1) ->
                  if
                    (match c with
                     | FStarC_Custard_Mono.Poly -> true
                     | uu___3 -> false)
                  then let uu___3 = go cs2 uf1 sp1 in u :: uu___3
                  else go cs2 uf1 sp1)
         | (uu___1, []) -> [] in
       go cs ub spine)
and call_type_args (st : state) (l : FStarC_Ident.lident)
  (cs : FStarC_Custard_Mono.bclass Prims.list)
  (spine : FStarC_Syntax_Syntax.args) : FStarC_Custard_Syntax.cty Prims.list=
  FStarC_Custard_Prof.timed "call_type_args"
    (fun uu___ ->
       let tflags = binder_flags st "t:" l FStarC_Custard_Mono.type_binders in
       let rec go cs1 tf sp =
         match (cs1, tf, sp) with
         | (c::cs2, t::tf1, (a, uu___1)::sp1) ->
             if
               t &&
                 (Prims.not
                    (match c with
                     | FStarC_Custard_Mono.Mono -> true
                     | uu___2 -> false))
             then
               let uu___2 = ty_of_typ st a in
               let uu___3 = go cs2 tf1 sp1 in uu___2 :: uu___3
             else go cs2 tf1 sp1
         | uu___1 -> [] in
       go cs tflags spine)
and callee_sig (st : state) (key : Prims.string)
  (tyargs : FStarC_Custard_Syntax.cty Prims.list) :
  FStarC_Custard_Syntax.cty=
  FStarC_Custard_Prof.timed "callee_sig"
    (fun uu___ ->
       let uu___1 = FStarC_SMap.try_find st.emitted key in
       match uu___1 with
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DLet d) ->
           let rec zip ps ts =
             match (ps, ts) with
             | (p::ps1, t::ts1) -> (p, t) :: (zip ps1 ts1)
             | uu___2 -> [] in
           let rec build bs =
             match bs with
             | [] -> d.FStarC_Custard_Syntax.dl_ret
             | b::[] ->
                 FStarC_Custard_Syntax.TArrow
                   ((b.FStarC_Custard_Syntax.b_ty),
                     (d.FStarC_Custard_Syntax.dl_eff),
                     (d.FStarC_Custard_Syntax.dl_ret))
             | b::bs1 ->
                 let uu___2 =
                   let uu___3 = build bs1 in
                   ((b.FStarC_Custard_Syntax.b_ty),
                     FStarC_Custard_Syntax.E_Pure, uu___3) in
                 FStarC_Custard_Syntax.TArrow uu___2 in
           let uu___2 = build d.FStarC_Custard_Syntax.dl_binders in
           FStarC_Custard_Syntax.subst_cty
             (zip d.FStarC_Custard_Syntax.dl_typars tyargs) uu___2
       | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DExternal d) ->
           let rec zipx ps ts =
             match (ps, ts) with
             | (p::ps1, t::ts1) -> (p, t) :: (zipx ps1 ts1)
             | (p::ps1, []) -> (p, FStarC_Custard_Syntax.TAny) ::
                 (zipx ps1 [])
             | ([], uu___2) -> [] in
           FStarC_Custard_Syntax.subst_cty
             (zipx d.FStarC_Custard_Syntax.dx_typars tyargs)
             d.FStarC_Custard_Syntax.dx_ty
       | uu___2 -> FStarC_Custard_Syntax.TAny)
and split_mono_args (st : state) (l : FStarC_Ident.lident)
  (cs : FStarC_Custard_Mono.bclass Prims.list)
  (spine : FStarC_Syntax_Syntax.args) :
  ((Prims.int * FStarC_Syntax_Syntax.term) Prims.list * (Prims.int *
    FStarC_Syntax_Syntax.term) Prims.list * FStarC_Syntax_Syntax.args *
    FStarC_Syntax_Syntax.bv Prims.list)=
  FStarC_Custard_Prof.timed "split_mono_args"
    (fun uu___ ->
       let uu___1 =
         let uu___2 =
           let uu___3 = FStarC_Custard_Mono.has_mono cs in Prims.not uu___3 in
         if uu___2
         then
           let uu___3 = FStarC_Custard_Mono.has_dropped cs in
           Prims.not uu___3
         else false in
       if uu___1
       then ([], [], spine, [])
       else
         (let n_args = FStarC_List.length spine in
          let rec go i cs1 sp margs msubst rest =
            match (cs1, sp) with
            | ([], uu___2) ->
                ((FStarC_List.rev margs), (FStarC_List.rev msubst),
                  (FStarC_List.op_At (FStarC_List.rev rest) sp))
            | ((FStarC_Custard_Mono.Poly)::cs2, a::sp1) ->
                go (i + Prims.int_one) cs2 sp1 margs msubst (a :: rest)
            | ((FStarC_Custard_Mono.Dropped)::cs2, uu___2::sp1) ->
                go (i + Prims.int_one) cs2 sp1 margs msubst rest
            | ((FStarC_Custard_Mono.Mono)::cs2, a::sp1) ->
                let a0 =
                  unfold_lets st (Prims.of_int 100)
                    (FStar_Pervasives_Native.fst a) in
                let what =
                  let uu___2 =
                    let uu___3 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                    Prims.strcat uu___3
                      (Prims.strcat " of " (FStarC_Ident.string_of_lid l)) in
                  Prims.strcat "the argument to binder " uu___2 in
                let w_opt = norm_optional st subst_norm_steps a0 in
                let w =
                  match w_opt with
                  | FStar_Pervasives_Native.Some w1 -> w1
                  | FStar_Pervasives_Native.None -> a0 in
                let t =
                  let uu___2 = norm_optional st key_norm_steps a0 in
                  match uu___2 with
                  | FStar_Pervasives_Native.Some t1 -> t1
                  | FStar_Pervasives_Native.None ->
                      ((let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_Options.custard_norm_budget () in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_int
                                        uu___11 in
                                    Prims.strcat uu___10 " steps)." in
                                  Prims.strcat
                                    " to a normal form within --custard_norm_budget ("
                                    uu___9 in
                                Prims.strcat what uu___8 in
                              Prims.strcat "Custard could not reduce " uu___7 in
                            FStarC_Errors_Msg.text uu___6 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        let uu___13 = tcenv st in
                                        FStarC_TypeChecker_Env.dsenv uu___13 in
                                      FStarC_Syntax_Print.term_to_string'
                                        uu___12 a0 in
                                    truncate_msg uu___11 in
                                  Prims.strcat
                                    "The argument, before reduction, was: "
                                    uu___10 in
                                FStarC_Errors_Msg.text uu___9 in
                              [uu___8] in
                            (FStarC_Errors_Msg.text
                               (Prims.strcat
                                  "This specialization is identified by "
                                  (Prims.strcat
                                     (if
                                        match w_opt with
                                        | FStar_Pervasives_Native.Some v ->
                                            true
                                        | uu___8 -> false
                                      then
                                        "the weak head normal form of its argument"
                                      else "the argument as written")
                                     " instead, which is correct but may compile the same code more than once. Raising --custard_norm_budget will not help if the argument is a value that shares subterms: reducing it is what destroys the sharing.")))
                              :: uu___7 in
                          uu___5 :: uu___6 in
                        custard_warning st
                          FStarC_Errors_Codes.Warning_CustardKeyNotReduced
                          uu___4);
                       w) in
                (check_mono_arg st l i t;
                 (let w1 =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Free.names w in
                      let uu___5 = FStarC_Syntax_Free.names t in
                      FStarC_Class_Setlike.subset
                        (FStarC_FlatSet.setlike_flat_set
                           FStarC_Syntax_Syntax.ord_bv) uu___4 uu___5 in
                    if uu___3 then w else t in
                  let uu___3 =
                    let before = builtin_type_rules st a0 in
                    let after = builtin_type_rules st t in
                    let uu___4 =
                      FStarC_List.existsb
                        (fun r ->
                           let uu___5 =
                             FStarC_List.existsb (fun s -> s = r) after in
                           Prims.not uu___5) before in
                    if uu___4 then (a0, a0) else (t, w1) in
                  match uu___3 with
                  | (t1, w2) ->
                      go (i + Prims.int_one) cs2 sp1 ((i, t1) :: margs)
                        ((i, w2) :: msubst) rest))
            | ((FStarC_Custard_Mono.Mono)::uu___2, []) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_nat n_args in
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int i in
                                Prims.strcat uu___12
                                  " is monomorphized and so must be given at every call site." in
                              Prims.strcat
                                " argument(s), but its binder number "
                                uu___11 in
                            Prims.strcat uu___9 uu___10 in
                          Prims.strcat " supplies only " uu___8 in
                        Prims.strcat (FStarC_Ident.string_of_lid l) uu___7 in
                      Prims.strcat "This use of " uu___6 in
                    FStarC_Errors_Msg.text uu___5 in
                  [uu___4;
                  FStarC_Errors_Msg.text
                    "Eta-expand the use, or drop the [@@monomorphize] attribute."] in
                custard_error st
                  FStarC_Errors_Codes.Error_CustardCannotMonomorphize uu___3
            | ((FStarC_Custard_Mono.Poly)::uu___2, []) ->
                ((FStarC_List.rev margs), (FStarC_List.rev msubst),
                  (FStarC_List.rev rest))
            | ((FStarC_Custard_Mono.Dropped)::uu___2, []) ->
                ((FStarC_List.rev margs), (FStarC_List.rev msubst),
                  (FStarC_List.rev rest)) in
          let uu___2 = go Prims.int_zero cs spine [] [] [] in
          match uu___2 with
          | (margs, msubst, rest) ->
              let holes = mono_holes st l margs msubst in
              (match holes with
               | [] -> (margs, msubst, rest, [])
               | uu___3 ->
                   let abs t =
                     let uu___4 =
                       FStarC_List.map FStarC_Syntax_Syntax.mk_binder holes in
                     FStarC_Syntax_Util.abs uu___4 t
                       FStar_Pervasives_Native.None in
                   let uu___4 =
                     FStarC_List.map
                       (fun uu___5 ->
                          match uu___5 with
                          | (i, t) -> let uu___6 = abs t in (i, uu___6))
                       margs in
                   let uu___5 =
                     FStarC_List.map
                       (fun uu___6 ->
                          match uu___6 with
                          | (i, t) -> let uu___7 = abs t in (i, uu___7))
                       msubst in
                   (uu___4, uu___5, rest, holes))))
and mono_holes (st : state) (l : FStarC_Ident.lident)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list)
  (msubst : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list) :
  FStarC_Syntax_Syntax.bv Prims.list=
  let names_of acc it =
    let uu___ =
      let uu___1 = FStarC_Syntax_Free.names (FStar_Pervasives_Native.snd it) in
      FStarC_Class_Setlike.elems
        (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv) uu___1 in
    FStarC_List.fold_left
      (fun acc1 v ->
         let uu___1 = FStarC_List.existsb (FStarC_Syntax_Syntax.bv_eq v) acc1 in
         if uu___1 then acc1 else FStarC_List.op_At acc1 [v]) acc uu___ in
  let vs = FStarC_List.fold_left names_of [] (FStarC_List.op_At margs msubst) in
  FStarC_List.sortWith
    (fun a b -> a.FStarC_Syntax_Syntax.index - b.FStarC_Syntax_Syntax.index)
    vs
and inlinable_local (st : state) (lb : FStarC_Syntax_Syntax.letbinding) :
  Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.unmeta lb.FStarC_Syntax_Syntax.lbdef in
      FStarC_Syntax_Subst.compress uu___2 in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.unmeta lb.FStarC_Syntax_Syntax.lbdef in
        FStarC_Syntax_Util.abs_formals uu___3 in
      (match uu___2 with
       | (bs, uu___3, uu___4) ->
           FStarC_List.existsb
             (fun b ->
                let uu___5 =
                  let uu___6 =
                    FStarC_Syntax_Subst.compress
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  uu___6.FStarC_Syntax_Syntax.n in
                match uu___5 with
                | FStarC_Syntax_Syntax.Tm_type uu___6 -> true
                | uu___6 -> false) bs)
  | uu___1 -> false
and unfold_lets (st : state) (fuel : Prims.int)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  if fuel <= Prims.int_zero
  then t
  else
    (let sub =
       let uu___ =
         let uu___1 = FStarC_Syntax_Free.names t in
         FStarC_Class_Setlike.elems
           (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv)
           uu___1 in
       FStarC_List.collect
         (fun bv ->
            let uu___1 =
              let uu___2 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int
                  bv.FStarC_Syntax_Syntax.index in
              FStarC_SMap.try_find st.letdefs uu___2 in
            match uu___1 with
            | FStar_Pervasives_Native.Some d ->
                [FStarC_Syntax_Syntax.NT (bv, d)]
            | FStar_Pervasives_Native.None -> []) uu___ in
     if match sub with | [] -> true | uu___ -> false
     then t
     else
       (let uu___ = FStarC_Syntax_Subst.subst sub t in
        unfold_lets st (fuel - Prims.int_one) uu___))
and check_mono_arg (st : state) (l : FStarC_Ident.lident) (i : Prims.int)
  (t : FStarC_Syntax_Syntax.term) : unit=
  (let uu___1 =
     let uu___2 = FStarC_Syntax_Subst.compress t in
     uu___2.FStarC_Syntax_Syntax.n in
   match uu___1 with
   | FStarC_Syntax_Syntax.Tm_name v ->
       let nm = FStarC_Ident.string_of_id v.FStarC_Syntax_Syntax.ppname in
       let where =
         let uu___2 =
           let uu___3 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
           Prims.strcat uu___3
             (Prims.strcat " of " (FStarC_Ident.string_of_lid l)) in
         Prims.strcat "the monomorphized binder number " uu___2 in
       let dynable =
         let uu___2 =
           let uu___3 =
             FStarC_Syntax_Subst.compress v.FStarC_Syntax_Syntax.sort in
           uu___3.FStarC_Syntax_Syntax.n in
         match uu___2 with
         | FStarC_Syntax_Syntax.Tm_type uu___3 -> false
         | uu___3 -> true in
       let dyn_hint lead =
         if dynable
         then
           [FStarC_Errors_Msg.text
              (Prims.strcat lead
                 (Prims.strcat "write [FStar.Custard.dyn "
                    (Prims.strcat nm "].")))]
         else [] in
       let msg =
         let uu___2 =
           let uu___3 =
             let uu___4 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int
                 v.FStarC_Syntax_Syntax.index in
             FStarC_SMap.try_find st.effletdefs uu___4 in
           match uu___3 with
           | FStar_Pervasives_Native.Some v1 -> true
           | uu___4 -> false in
         if uu___2
         then
           FStarC_List.op_At
             [FStarC_Errors_Msg.text
                (Prims.strcat "The argument passed to "
                   (Prims.strcat where
                      (Prims.strcat " is "
                         (Prims.strcat nm
                            ", the result of an effectful computation, so the whole argument is a hole (section 3.2c) and no skeleton is left to specialize on."))));
             FStarC_Errors_Msg.text
               (Prims.strcat
                  "Unlike a runtime parameter, this cannot be fixed by an annotation: the computation runs when the program runs, so "
                  (Prims.strcat nm
                     " is never known earlier.  What is left is to pass the value at runtime -- for a typeclass dictionary, ordinary dictionary passing -- which is the identity-skeleton end of section 3.2c."))]
             (FStarC_List.op_At (dyn_hint "To ask for that here, ")
                [FStarC_Errors_Msg.text
                   "It is opt-in, and per call site, because it reintroduces the indirect calls monomorphization exists to remove: other calls to this function are still specialized."])
         else
           (let uu___3 =
              let uu___4 =
                let uu___5 = tcenv st in
                FStarC_Custard_Mono.existential_field uu___5
                  (FStarC_Syntax_Syntax.mk_binder v) in
              match uu___4 with
              | FStar_Pervasives_Native.Some (c, f) ->
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_int i in
                        Prims.strcat uu___8
                          (Prims.strcat
                             " to drop: it is monomorphized because its type stores a Type0 in the field "
                             (Prims.strcat
                                (FStarC_Ident.string_of_id
                                   (FStarC_Ident.ident_of_lid f))
                                (Prims.strcat " of "
                                   (Prims.strcat
                                      (FStarC_Ident.string_of_lid c)
                                      ", and a later field's type mentions it (rule 4b, section 30.9).")))) in
                      Prims.strcat "There is no annotation on binder " uu___7 in
                    FStarC_Errors_Msg.text uu___6 in
                  [uu___5;
                  FStarC_Errors_Msg.text
                    "That makes the type an existential package: what a value of it looks like at runtime depends on the type it carries, so there is no one C representation to pass it in, and no annotation changes that (section 30.3).";
                  FStarC_Errors_Msg.text
                    (Prims.strcat
                       "What does work is to make the type a *parameter* -- move it off "
                       (Prims.strcat (FStarC_Ident.string_of_lid c)
                          " and onto the inductive, so that the type is fixed by the type rather than by the value -- or to keep the existential out of runtime data by specializing every use of it."))]
              | FStar_Pervasives_Native.None ->
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_int i in
                              Prims.strcat uu___11 " and pass it at runtime." in
                            Prims.strcat
                              " with [@@monomorphize] in the enclosing definition so that it, too, is known at specialization time, or drop the annotation on binder "
                              uu___10 in
                          Prims.strcat nm uu___9 in
                        Prims.strcat "Mark " uu___8 in
                      FStarC_Errors_Msg.text uu___7 in
                    [uu___6] in
                  FStarC_List.op_At uu___5
                    (dyn_hint
                       "To pass it at runtime at this call site only, without changing either signature, ") in
            FStarC_List.op_At
              [FStarC_Errors_Msg.text
                 (Prims.strcat "The argument passed to "
                    (Prims.strcat where
                       (Prims.strcat " is the runtime parameter "
                          (Prims.strcat nm
                             ", so there is nothing to specialize on."))))]
              uu___3) in
       custard_error st FStarC_Errors_Codes.Error_CustardCannotMonomorphize
         msg
   | uu___2 -> ());
  (let is_type_name v =
     let uu___1 =
       let uu___2 = FStarC_Syntax_Subst.compress v.FStarC_Syntax_Syntax.sort in
       uu___2.FStarC_Syntax_Syntax.n in
     match uu___1 with
     | FStarC_Syntax_Syntax.Tm_type uu___2 -> true
     | uu___2 -> false in
   let uu___1 =
     let uu___2 =
       let uu___3 = FStarC_Syntax_Free.names t in
       FStarC_Class_Setlike.elems
         (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv) uu___3 in
     FStarC_List.filter is_type_name uu___2 in
   match uu___1 with
   | [] -> ()
   | v::uu___2 ->
       let uu___3 =
         let uu___4 =
           let uu___5 =
             let uu___6 =
               let uu___7 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
               Prims.strcat uu___7
                 (Prims.strcat " of "
                    (Prims.strcat (FStarC_Ident.string_of_lid l)
                       (Prims.strcat
                          " is not known at specialization time: it mentions the runtime type parameter "
                          (Prims.strcat
                             (FStarC_Ident.string_of_id
                                v.FStarC_Syntax_Syntax.ppname) ".")))) in
             Prims.strcat
               "The argument passed to the monomorphized binder number "
               uu___6 in
           FStarC_Errors_Msg.text uu___5 in
         let uu___5 =
           let uu___6 =
             let uu___7 =
               let uu___8 =
                 let uu___9 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int
                     v.FStarC_Syntax_Syntax.index in
                 FStarC_SMap.try_find st.defbinders uu___9 in
               match uu___8 with
               | FStar_Pervasives_Native.Some v1 -> true
               | uu___9 -> false in
             if uu___7
             then
               FStarC_Errors_Msg.text
                 (Prims.strcat "Mark "
                    (Prims.strcat
                       (FStarC_Ident.string_of_id
                          v.FStarC_Syntax_Syntax.ppname)
                       " with [@@monomorphize] in the enclosing definition so that it, too, is known at specialization time.  (A runtime *value* would be passed at runtime instead -- see section 3.2c -- but a type is erased, so there would be nothing to pass.)"))
             else
               FStarC_Errors_Msg.text
                 (Prims.strcat
                    (FStarC_Ident.string_of_id v.FStarC_Syntax_Syntax.ppname)
                    " is not a parameter of the enclosing definition, so there is nowhere to write [@@monomorphize]: the attribute classifies the arguments of a function (section 3.2), and writing it on a constructor field is read by nothing.  A type that arrives as a field rather than as a parameter makes its record an existential package, which section 30.3 records as unsupported.") in
           [uu___6] in
         uu___4 :: uu___5 in
       custard_error st FStarC_Errors_Codes.Error_CustardCannotMonomorphize
         uu___3)
and callee_eff (st : state) (key : Prims.string) (n_args : Prims.int) :
  FStarC_Custard_Syntax.eff=
  let uu___ = FStarC_SMap.try_find st.emitted key in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DLet l) ->
      let n = FStarC_List.length l.FStarC_Custard_Syntax.dl_binders in
      if n_args < n
      then FStarC_Custard_Syntax.E_Pure
      else
        (let uu___1 =
           apply_eff st l.FStarC_Custard_Syntax.dl_ret (n_args - n) in
         FStarC_Custard_Syntax.join_eff l.FStarC_Custard_Syntax.dl_eff uu___1)
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DExternal x) ->
      apply_eff st x.FStarC_Custard_Syntax.dx_ty n_args
  | uu___1 -> FStarC_Custard_Syntax.E_Impure
and branch_of_branch (st : state) (br : FStarC_Syntax_Syntax.branch) :
  FStarC_Custard_Syntax.branch=
  let uu___ = FStarC_Syntax_Subst.open_branch br in
  match uu___ with
  | (p, g, b) ->
      let uu___1 = pat_of_pat st p in
      let uu___2 =
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g1 ->
            let uu___3 = expr_of_term st g1 in
            FStar_Pervasives_Native.Some uu___3 in
      let uu___3 = expr_of_term st b in (uu___1, uu___2, uu___3)
and pat_of_pat (st : state) (p : FStarC_Syntax_Syntax.pat) :
  FStarC_Custard_Syntax.pat=
  match p.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_constant c ->
      let uu___ = constant_of_sconst c in
      (match uu___ with
       | FStar_Pervasives_Native.Some c1 -> FStarC_Custard_Syntax.PConst c1
       | FStar_Pervasives_Native.None -> FStarC_Custard_Syntax.PWild)
  | FStarC_Syntax_Syntax.Pat_var bv ->
      let uu___ = name_of_bv bv in FStarC_Custard_Syntax.PVar uu___
  | FStarC_Syntax_Syntax.Pat_dot_term uu___ -> FStarC_Custard_Syntax.PWild
  | FStarC_Syntax_Syntax.Pat_cons (fv, uu___, pats) ->
      let l = FStarC_Syntax_Syntax.lid_of_fv fv in
      let flags = ctor_dropped_flags st l in
      let pats1 =
        let uu___1 = drop_flagged flags pats in
        FStarC_List.map
          (fun uu___2 -> match uu___2 with | (p1, uu___3) -> pat_of_pat st p1)
          uu___1 in
      let uu___1 =
        let uu___2 =
          request st
            {
              sk_lid = l;
              sk_args = [];
              sk_subst = [];
              sk_holes = Prims.int_zero
            } in
        (uu___2, pats1) in
      FStarC_Custard_Syntax.PCtor uu___1
and reference_flags (l : FStarC_Ident.lident)
  (attrs : FStarC_Syntax_Syntax.term Prims.list) (is_extern : Prims.bool) :
  FStarC_Custard_Syntax.flag Prims.list=
  let uu___ =
    let uu___1 =
      FStarC_Syntax_Util.has_attribute attrs
        FStarC_Parser_Const.custard_c_reference_attr in
    Prims.not uu___1 in
  if uu___
  then []
  else
    (if Prims.not is_extern
     then
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Error_CustardBadReference
         () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic
            [FStarC_Errors_Msg.text
               (Prims.strcat "Custard: [@@custard_c_reference] is on "
                  (Prims.strcat (FStarC_Ident.string_of_lid l)
                     ", which is not an external type."));
            FStarC_Errors_Msg.text
              "It says that values of the type are handles, so a binding of one has to alias rather than copy -- which is a statement about how the target spells a binding, and a type Custard compiles itself has no target spelling to differ from.";
            FStarC_Errors_Msg.text
              "Add a [@@custard_extern] target, or drop the attribute."])
     else ();
     [FStarC_Custard_Syntax.CReference])
and extract_lid (st : state) (l : FStarC_Ident.lident)
  (nm : FStarC_Custard_Syntax.name)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list)
  (n_holes : Prims.int) : FStarC_Custard_Syntax.decl=
  let se =
    FStarC_Custard_Prof.timed "sigelt"
      (fun uu___ ->
         let uu___1 =
           let uu___2 = tcenv st in
           FStarC_TypeChecker_Env.lookup_sigelt uu___2 l in
         FStarC_Option.map
           (fun se1 ->
              let uu___2 = fixup_normalize_for_extraction st se1 in
              fixup_extract_as uu___2) uu___1) in
  let rule =
    match se with
    | FStar_Pervasives_Native.Some se1 ->
        let uu___ =
          FStarC_Custard_Builtins.rule_of_attributes
            se1.FStarC_Syntax_Syntax.sigattrs in
        (match uu___ with
         | FStar_Pervasives_Native.Some r -> FStar_Pervasives_Native.Some r
         | FStar_Pervasives_Native.None ->
             FStarC_Custard_Builtins.lookup_rule l)
    | FStar_Pervasives_Native.None -> FStarC_Custard_Builtins.lookup_rule l in
  match rule with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_extern x) when
      match se with
      | FStar_Pervasives_Native.Some
          {
            FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
              { FStarC_Syntax_Syntax.lid2 = uu___;
                FStarC_Syntax_Syntax.us2 = uu___1;
                FStarC_Syntax_Syntax.t2 = t;_};
            FStarC_Syntax_Syntax.sigrng = uu___2;
            FStarC_Syntax_Syntax.sigquals = uu___3;
            FStarC_Syntax_Syntax.sigmeta = uu___4;
            FStarC_Syntax_Syntax.sigattrs = uu___5;
            FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
            FStarC_Syntax_Syntax.sigopts = uu___7;_}
          -> is_type_sig st t
      | uu___ -> false ->
      let t =
        match se with
        | FStar_Pervasives_Native.Some
            {
              FStarC_Syntax_Syntax.sigel =
                FStarC_Syntax_Syntax.Sig_declare_typ
                { FStarC_Syntax_Syntax.lid2 = uu___;
                  FStarC_Syntax_Syntax.us2 = uu___1;
                  FStarC_Syntax_Syntax.t2 = t1;_};
              FStarC_Syntax_Syntax.sigrng = uu___2;
              FStarC_Syntax_Syntax.sigquals = uu___3;
              FStarC_Syntax_Syntax.sigmeta = uu___4;
              FStarC_Syntax_Syntax.sigattrs = uu___5;
              FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
              FStarC_Syntax_Syntax.sigopts = uu___7;_}
            -> t1
        | uu___ -> FStarC_Effect.failwith "unreachable" in
      let uu___ = FStarC_Syntax_Util.arrow_formals t in
      (match uu___ with
       | (bs, uu___1) ->
           let tmpl =
             let uu___2 = extern_template st l in
             match uu___2 with
             | FStar_Pervasives_Native.Some v -> true
             | uu___3 -> false in
           let ps =
             FStarC_List.collect
               (fun b ->
                  let uu___2 =
                    if tmpl
                    then true
                    else
                      (let uu___3 = tcenv st in
                       FStarC_Custard_Mono.is_type_param uu___3 b) in
                  if uu___2
                  then
                    let uu___3 = name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                    [uu___3]
                  else []) bs in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 match se with
                 | FStar_Pervasives_Native.Some se1 ->
                     reference_flags l se1.FStarC_Syntax_Syntax.sigattrs true
                 | FStar_Pervasives_Native.None -> [] in
               FStarC_List.op_At
                 [FStarC_Custard_Syntax.Extern
                    ((x.FStarC_Custard_Builtins.x_name),
                      (x.FStarC_Custard_Builtins.x_header));
                 FStarC_Custard_Syntax.NoNewtype] uu___4 in
             {
               FStarC_Custard_Syntax.dt_name = nm;
               FStarC_Custard_Syntax.dt_params = ps;
               FStarC_Custard_Syntax.dt_body =
                 FStarC_Custard_Syntax.TAbstract;
               FStarC_Custard_Syntax.dt_flags = uu___3
             } in
           FStarC_Custard_Syntax.DType uu___2)
  | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_extern x) ->
      let uu___ = external_ty st l margs in
      (match uu___ with
       | (typars, ty) ->
           FStarC_Custard_Syntax.DExternal
             {
               FStarC_Custard_Syntax.dx_name = nm;
               FStarC_Custard_Syntax.dx_typars = typars;
               FStarC_Custard_Syntax.dx_ty = ty;
               FStarC_Custard_Syntax.dx_target =
                 (x.FStarC_Custard_Builtins.x_name);
               FStarC_Custard_Syntax.dx_header =
                 (x.FStarC_Custard_Builtins.x_header);
               FStarC_Custard_Syntax.dx_flags = []
             })
  | uu___ ->
      let is_opaque =
        match rule with
        | FStar_Pervasives_Native.Some (FStarC_Custard_Builtins.Rule_opaque)
            -> true
        | uu___1 -> false in
      let is_realized =
        match rule with
        | FStar_Pervasives_Native.Some
            (FStarC_Custard_Builtins.Rule_realized) -> true
        | uu___1 -> false in
      (match se with
       | FStar_Pervasives_Native.None ->
           custard_error st FStarC_Errors_Codes.Error_CustardEntryNotFound
             [FStarC_Errors_Msg.text
                (Prims.strcat "Custard cannot find a definition for "
                   (Prims.strcat (FStarC_Ident.string_of_lid l) "."))]
       | FStar_Pervasives_Native.Some se1 when
           let uu___1 =
             let uu___2 =
               if
                 is_realized &&
                   (match se1.FStarC_Syntax_Syntax.sigel with
                    | FStarC_Syntax_Syntax.Sig_let _0 -> true
                    | uu___3 -> false)
               then let uu___3 = is_inlinable se1 in Prims.not uu___3
               else false in
             if uu___2
             then
               let uu___3 = is_inline_for_extraction st se1 in
               Prims.not uu___3
             else false in
           if uu___1
           then
             let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStarC_List.map FStarC_Ident.string_of_id
                     (FStarC_Ident.ns_of_lid l) in
                 FStarC_Custard_Builtins.no_fstar_stubs uu___4 in
               FStarC_Custard_Builtins.is_type_only_realized_module uu___3 in
             Prims.not uu___2
           else false ->
           let uu___1 = external_ty st l margs in
           (match uu___1 with
            | (typars, ty) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 = is_c_backend () in
                    if uu___4
                    then c_realized_header l
                    else FStar_Pervasives_Native.None in
                  let uu___4 =
                    let uu___5 = is_modelled_lid l in
                    if uu___5 then [FStarC_Custard_Syntax.Modelled] else [] in
                  {
                    FStarC_Custard_Syntax.dx_name = nm;
                    FStarC_Custard_Syntax.dx_typars = typars;
                    FStarC_Custard_Syntax.dx_ty = ty;
                    FStarC_Custard_Syntax.dx_target =
                      FStar_Pervasives_Native.None;
                    FStarC_Custard_Syntax.dx_header = uu___3;
                    FStarC_Custard_Syntax.dx_flags = uu___4
                  } in
                FStarC_Custard_Syntax.DExternal uu___2)
       | FStar_Pervasives_Native.Some se1 ->
           let d =
             FStarC_Custard_Prof.timed "extract_sigelt"
               (fun uu___1 -> extract_sigelt st l nm margs n_holes se1) in
           let d1 = if is_opaque || is_realized then with_no_newtype d else d in
           let inlined =
             FStarC_List.existsb
               (fun q ->
                  (q = FStarC_Syntax_Syntax.Inline_for_extraction) ||
                    (q =
                       FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen))
               se1.FStarC_Syntax_Syntax.sigquals in
           let d2 =
             if Prims.not (is_realized && (Prims.not inlined))
             then d1
             else
               (let uu___1 =
                  let uu___2 = is_c_backend () in
                  if uu___2
                  then c_realized_header l
                  else FStar_Pervasives_Native.None in
                match uu___1 with
                | FStar_Pervasives_Native.Some h -> with_c_realized h d1
                | FStar_Pervasives_Native.None -> with_realized d1) in
           let d3 =
             let uu___1 =
               let uu___2 = is_modelled_lid l in
               if uu___2 then Prims.not inlined else false in
             if uu___1 then with_modelled d2 else d2 in
           let uu___1 =
             let uu___2 = is_inlinable se1 in
             if uu___2
             then let uu___3 = is_root st l in Prims.not uu___3
             else false in
           if uu___1 then with_inline d3 else d3)
and fixup_extract_as (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Syntax_Syntax.sigelt=
  let uu___ =
    let uu___1 =
      FStarC_List.tryPick FStarC_Parser_Const_ExtractAs.is_extract_as_attr
        se.FStarC_Syntax_Syntax.sigattrs in
    ((se.FStarC_Syntax_Syntax.sigel), uu___1) in
  match uu___ with
  | (FStarC_Syntax_Syntax.Sig_let
     { FStarC_Syntax_Syntax.lbs1 = (is_rec, lb::[]);
       FStarC_Syntax_Syntax.lids1 = lids;_},
     FStar_Pervasives_Native.Some impl) ->
      let self =
        match lb.FStarC_Syntax_Syntax.lbname with
        | FStar_Pervasives.Inr fv ->
            let uu___1 = FStarC_Syntax_Free.fvars impl in
            FStarC_Class_Setlike.mem
              (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv)
              (FStarC_Syntax_Syntax.lid_of_fv fv) uu___1
        | FStar_Pervasives.Inl uu___1 -> false in
      {
        FStarC_Syntax_Syntax.sigel =
          (FStarC_Syntax_Syntax.Sig_let
             {
               FStarC_Syntax_Syntax.lbs1 =
                 ((is_rec || self),
                   [{
                      FStarC_Syntax_Syntax.lbname =
                        (lb.FStarC_Syntax_Syntax.lbname);
                      FStarC_Syntax_Syntax.lbunivs =
                        (lb.FStarC_Syntax_Syntax.lbunivs);
                      FStarC_Syntax_Syntax.lbtyp =
                        (lb.FStarC_Syntax_Syntax.lbtyp);
                      FStarC_Syntax_Syntax.lbeff =
                        (lb.FStarC_Syntax_Syntax.lbeff);
                      FStarC_Syntax_Syntax.lbdef = impl;
                      FStarC_Syntax_Syntax.lbattrs =
                        (lb.FStarC_Syntax_Syntax.lbattrs);
                      FStarC_Syntax_Syntax.lbpos =
                        (lb.FStarC_Syntax_Syntax.lbpos)
                    }]);
               FStarC_Syntax_Syntax.lids1 = lids
             });
        FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = (se.FStarC_Syntax_Syntax.sigquals);
        FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
      }
  | (FStarC_Syntax_Syntax.Sig_declare_typ
     { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = us;
       FStarC_Syntax_Syntax.t2 = t;_},
     FStar_Pervasives_Native.Some impl) ->
      let fv =
        FStarC_Syntax_Syntax.lid_as_fv lid FStar_Pervasives_Native.None in
      let lb =
        FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inr fv) us t
          FStarC_Parser_Const.effect_Tot_lid impl []
          se.FStarC_Syntax_Syntax.sigrng in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Syntax_Free.fvars impl in
              FStarC_Class_Setlike.mem
                (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_fv) lid
                uu___5 in
            (uu___4, [lb]) in
          {
            FStarC_Syntax_Syntax.lbs1 = uu___3;
            FStarC_Syntax_Syntax.lids1 = [lid]
          } in
        FStarC_Syntax_Syntax.Sig_let uu___2 in
      {
        FStarC_Syntax_Syntax.sigel = uu___1;
        FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals =
          (FStarC_Syntax_Syntax.Inline_for_extraction ::
          (se.FStarC_Syntax_Syntax.sigquals));
        FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
      }
  | uu___1 -> se
and assumed_projector_lb (st : state) (se : FStarC_Syntax_Syntax.sigelt)
  (l : FStarC_Ident.lident) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.letbinding FStar_Pervasives_Native.option=
  let env = tcenv st in
  let uu___ =
    FStarC_List.tryPick
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Syntax_Syntax.Projector (c, f) ->
             FStar_Pervasives_Native.Some
               (c, (FStar_Pervasives_Native.Some f))
         | FStarC_Syntax_Syntax.Discriminator c ->
             FStar_Pervasives_Native.Some (c, FStar_Pervasives_Native.None)
         | uu___2 -> FStar_Pervasives_Native.None)
      se.FStarC_Syntax_Syntax.sigquals in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ctor, field) ->
      let uu___1 = FStarC_Syntax_Util.arrow_formals_comp t in
      (match uu___1 with
       | (bs, uu___2) ->
           let ind = FStarC_TypeChecker_Env.typ_of_datacon env ctor in
           let is_projectee b =
             let uu___3 =
               let uu___4 =
                 FStarC_Custard_Mono.strip
                   (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
               FStarC_Syntax_Util.leftmost_head_and_args uu___4 in
             match uu___3 with
             | (hd, uu___4) ->
                 let uu___5 =
                   let uu___6 = FStarC_Syntax_Subst.compress hd in
                   uu___6.FStarC_Syntax_Syntax.n in
                 (match uu___5 with
                  | FStarC_Syntax_Syntax.Tm_fvar fv ->
                      FStarC_Ident.lid_equals
                        (FStarC_Syntax_Syntax.lid_of_fv fv) ind
                  | FStarC_Syntax_Syntax.Tm_uinst
                      ({
                         FStarC_Syntax_Syntax.n =
                           FStarC_Syntax_Syntax.Tm_fvar fv;
                         FStarC_Syntax_Syntax.pos = uu___6;
                         FStarC_Syntax_Syntax.hash_code = uu___7;_},
                       uu___8)
                      ->
                      FStarC_Ident.lid_equals
                        (FStarC_Syntax_Syntax.lid_of_fv fv) ind
                  | uu___6 -> false) in
           let rec split_at_projectee bs1 =
             match bs1 with
             | [] -> FStar_Pervasives_Native.None
             | b::rest ->
                 let uu___3 = is_projectee b in
                 if uu___3
                 then FStar_Pervasives_Native.Some (b, rest)
                 else split_at_projectee rest in
           let uu___3 = split_at_projectee bs in
           (match uu___3 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (projectee, post) ->
                let uu___4 = FStarC_TypeChecker_Env.lookup_datacon env ctor in
                (match uu___4 with
                 | (uu___5, cty) ->
                     let uu___6 = FStarC_Syntax_Util.arrow_formals cty in
                     (match uu___6 with
                      | (all_params, uu___7) ->
                          let ntps =
                            let uu___8 =
                              let uu___9 =
                                FStarC_TypeChecker_Env.typ_of_datacon env
                                  ctor in
                              FStarC_TypeChecker_Env.num_inductive_ty_params
                                env uu___9 in
                            match uu___8 with
                            | FStar_Pervasives_Native.Some n -> n
                            | FStar_Pervasives_Native.None -> Prims.int_zero in
                          let var x =
                            FStarC_Syntax_Syntax.withinfo
                              (FStarC_Syntax_Syntax.Pat_var x)
                              FStarC_Range_Type.dummyRange in
                          let fresh b =
                            let uu___8 =
                              FStarC_Syntax_Syntax.gen_bv
                                (FStarC_Ident.string_of_id
                                   (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                                FStar_Pervasives_Native.None
                                FStarC_Syntax_Syntax.tun in
                            var uu___8 in
                          let ctor_pat chosen =
                            let args =
                              FStarC_List.mapi
                                (fun j b ->
                                   let imp =
                                     FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                                       b.FStarC_Syntax_Syntax.binder_qual in
                                   let p =
                                     if imp && (j < ntps)
                                     then
                                       FStarC_Syntax_Syntax.withinfo
                                         (FStarC_Syntax_Syntax.Pat_dot_term
                                            FStar_Pervasives_Native.None)
                                         FStarC_Range_Type.dummyRange
                                     else fresh b in
                                   (p, imp)) all_params in
                            FStarC_Syntax_Syntax.withinfo
                              (FStarC_Syntax_Syntax.Pat_cons
                                 ((FStarC_Syntax_Syntax.lid_as_fv ctor
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None, args))
                              FStarC_Range_Type.dummyRange in
                          let scrut =
                            FStarC_Syntax_Syntax.bv_to_name
                              projectee.FStarC_Syntax_Syntax.binder_bv in
                          let body =
                            match field with
                            | FStar_Pervasives_Native.None ->
                                let pt =
                                  ctor_pat FStar_Pervasives_Native.None in
                                let pf =
                                  let uu___8 =
                                    FStarC_Syntax_Syntax.new_bv
                                      FStar_Pervasives_Native.None
                                      FStarC_Syntax_Syntax.tun in
                                  var uu___8 in
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStarC_Syntax_Util.branch
                                            (pt,
                                              FStar_Pervasives_Native.None,
                                              FStarC_Syntax_Util.exp_true_bool) in
                                        let uu___13 =
                                          let uu___14 =
                                            FStarC_Syntax_Util.branch
                                              (pf,
                                                FStar_Pervasives_Native.None,
                                                FStarC_Syntax_Util.exp_false_bool) in
                                          [uu___14] in
                                        uu___12 :: uu___13 in
                                      {
                                        FStarC_Syntax_Syntax.scrutinee =
                                          scrut;
                                        FStarC_Syntax_Syntax.ret_opt =
                                          FStar_Pervasives_Native.None;
                                        FStarC_Syntax_Syntax.brs = uu___11;
                                        FStarC_Syntax_Syntax.rc_opt1 =
                                          FStar_Pervasives_Native.None
                                      } in
                                    FStarC_Syntax_Syntax.Tm_match uu___10 in
                                  FStarC_Syntax_Syntax.mk uu___9
                                    FStarC_Range_Type.dummyRange in
                                FStar_Pervasives_Native.Some uu___8
                            | FStar_Pervasives_Native.Some f ->
                                let fname = FStarC_Ident.string_of_id f in
                                let uu___8 =
                                  let uu___9 =
                                    FStarC_List.mapi
                                      (fun j b ->
                                         if
                                           (j >= ntps) &&
                                             ((FStarC_Ident.string_of_id
                                                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                                                = fname)
                                         then [j]
                                         else []) all_params in
                                  FStarC_List.flatten uu___9 in
                                (match uu___8 with
                                 | [] -> FStar_Pervasives_Native.None
                                 | j::uu___9 ->
                                     let x =
                                       FStarC_Syntax_Syntax.gen_bv fname
                                         FStar_Pervasives_Native.None
                                         FStarC_Syntax_Syntax.tun in
                                     let args =
                                       FStarC_List.mapi
                                         (fun k b ->
                                            let imp =
                                              FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                                                b.FStarC_Syntax_Syntax.binder_qual in
                                            let p =
                                              if k = j
                                              then var x
                                              else
                                                if imp && (k < ntps)
                                                then
                                                  FStarC_Syntax_Syntax.withinfo
                                                    (FStarC_Syntax_Syntax.Pat_dot_term
                                                       FStar_Pervasives_Native.None)
                                                    FStarC_Range_Type.dummyRange
                                                else fresh b in
                                            (p, imp)) all_params in
                                     let pat =
                                       FStarC_Syntax_Syntax.withinfo
                                         (FStarC_Syntax_Syntax.Pat_cons
                                            ((FStarC_Syntax_Syntax.lid_as_fv
                                                ctor
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None,
                                              args))
                                         FStarC_Range_Type.dummyRange in
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               let uu___15 =
                                                 let uu___16 =
                                                   FStarC_Syntax_Syntax.bv_to_name
                                                     x in
                                                 (pat,
                                                   FStar_Pervasives_Native.None,
                                                   uu___16) in
                                               FStarC_Syntax_Util.branch
                                                 uu___15 in
                                             [uu___14] in
                                           {
                                             FStarC_Syntax_Syntax.scrutinee =
                                               scrut;
                                             FStarC_Syntax_Syntax.ret_opt =
                                               FStar_Pervasives_Native.None;
                                             FStarC_Syntax_Syntax.brs =
                                               uu___13;
                                             FStarC_Syntax_Syntax.rc_opt1 =
                                               FStar_Pervasives_Native.None
                                           } in
                                         FStarC_Syntax_Syntax.Tm_match
                                           uu___12 in
                                       FStarC_Syntax_Syntax.mk uu___11
                                         FStarC_Range_Type.dummyRange in
                                     FStar_Pervasives_Native.Some uu___10) in
                          (match body with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some body1 ->
                               let body2 =
                                 match post with
                                 | [] -> body1
                                 | uu___8 ->
                                     let uu___9 =
                                       FStarC_List.map
                                         (fun b ->
                                            let uu___10 =
                                              FStarC_Syntax_Syntax.bv_to_name
                                                b.FStarC_Syntax_Syntax.binder_bv in
                                            FStarC_Syntax_Syntax.as_arg
                                              uu___10) post in
                                     FStarC_Syntax_Syntax.mk_Tm_app body1
                                       uu___9 FStarC_Range_Type.dummyRange in
                               let uu___8 =
                                 let uu___9 =
                                   FStarC_Syntax_Util.abs bs body2
                                     FStar_Pervasives_Native.None in
                                 FStarC_Syntax_Util.mk_letbinding
                                   (FStar_Pervasives.Inr
                                      (FStarC_Syntax_Syntax.lid_and_dd_as_fv
                                         l FStar_Pervasives_Native.None)) []
                                   t FStarC_Parser_Const.effect_Tot_lid
                                   uu___9 [] FStarC_Range_Type.dummyRange in
                               FStar_Pervasives_Native.Some uu___8)))))
and is_inline_for_extraction (st : state) (se : FStarC_Syntax_Syntax.sigelt)
  : Prims.bool=
  let uu___ =
    FStarC_List.existsb
      (fun q -> q = FStarC_Syntax_Syntax.Inline_for_extraction)
      se.FStarC_Syntax_Syntax.sigquals in
  if uu___
  then true
  else
    (match se.FStarC_Syntax_Syntax.sigel with
     | FStarC_Syntax_Syntax.Sig_let
         { FStarC_Syntax_Syntax.lbs1 = (uu___1, lb::[]);
           FStarC_Syntax_Syntax.lids1 = uu___2;_}
         ->
         let uu___3 =
           FStarC_Syntax_Util.arrow_formals_comp
             lb.FStarC_Syntax_Syntax.lbtyp in
         (match uu___3 with
          | (uu___4, c) ->
              let uu___5 = tcenv st in
              let uu___6 =
                let uu___7 =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    (FStarC_Syntax_Util.comp_result c) in
                FStarC_Syntax_Syntax.mk_binder uu___7 in
              FStarC_Custard_Mono.is_type_binder uu___5 uu___6)
     | uu___1 -> false)
and is_inlinable (se : FStarC_Syntax_Syntax.sigelt) : Prims.bool=
  let uu___ =
    FStarC_List.existsb
      (fun q ->
         match q with
         | FStarC_Syntax_Syntax.Projector uu___1 -> true
         | FStarC_Syntax_Syntax.Discriminator uu___1 -> true
         | uu___1 -> false) se.FStarC_Syntax_Syntax.sigquals in
  if uu___
  then true
  else
    (let uu___1 =
       FStarC_List.existsb
         (fun q -> q = FStarC_Syntax_Syntax.Inline_for_extraction)
         se.FStarC_Syntax_Syntax.sigquals in
     if uu___1
     then
       let uu___2 =
         FStarC_List.tryPick FStarC_Parser_Const_ExtractAs.is_extract_as_attr
           se.FStarC_Syntax_Syntax.sigattrs in
       match uu___2 with
       | FStar_Pervasives_Native.Some v -> true
       | uu___3 -> false
     else false)
and with_inline (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DLet l when
      let uu___ =
        FStarC_List.existsb FStarC_Custard_Syntax.uu___is_Rec
          l.FStarC_Custard_Syntax.dl_flags in
      Prims.not uu___ ->
      FStarC_Custard_Syntax.DLet
        {
          FStarC_Custard_Syntax.dl_name = (l.FStarC_Custard_Syntax.dl_name);
          FStarC_Custard_Syntax.dl_typars =
            (l.FStarC_Custard_Syntax.dl_typars);
          FStarC_Custard_Syntax.dl_binders =
            (l.FStarC_Custard_Syntax.dl_binders);
          FStarC_Custard_Syntax.dl_ret = (l.FStarC_Custard_Syntax.dl_ret);
          FStarC_Custard_Syntax.dl_eff = (l.FStarC_Custard_Syntax.dl_eff);
          FStarC_Custard_Syntax.dl_body = (l.FStarC_Custard_Syntax.dl_body);
          FStarC_Custard_Syntax.dl_flags = (FStarC_Custard_Syntax.Inline ::
            (l.FStarC_Custard_Syntax.dl_flags))
        }
  | d1 -> d1
and with_no_newtype (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_List.filter
              (fun f ->
                 Prims.not
                   (match f with
                    | FStarC_Custard_Syntax.Erased -> true
                    | uu___3 -> false)) t.FStarC_Custard_Syntax.dt_flags in
          FStarC_Custard_Syntax.NoNewtype :: uu___2 in
        {
          FStarC_Custard_Syntax.dt_name = (t.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (t.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = (t.FStarC_Custard_Syntax.dt_body);
          FStarC_Custard_Syntax.dt_flags = uu___1
        } in
      FStarC_Custard_Syntax.DType uu___
  | d1 -> d1
and with_realized (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      FStarC_Custard_Syntax.DType
        {
          FStarC_Custard_Syntax.dt_name = (t.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (t.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = (t.FStarC_Custard_Syntax.dt_body);
          FStarC_Custard_Syntax.dt_flags = (FStarC_Custard_Syntax.Realized ::
            (t.FStarC_Custard_Syntax.dt_flags))
        }
  | d1 -> d1
and with_c_realized (h : Prims.string) (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStarC_Custard_Syntax.mangled_name
                    t.FStarC_Custard_Syntax.dt_name in
                FStar_Pervasives_Native.Some uu___5 in
              (uu___4, (FStar_Pervasives_Native.Some h)) in
            FStarC_Custard_Syntax.Extern uu___3 in
          uu___2 :: FStarC_Custard_Syntax.NoNewtype ::
            (t.FStarC_Custard_Syntax.dt_flags) in
        {
          FStarC_Custard_Syntax.dt_name = (t.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (t.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = FStarC_Custard_Syntax.TAbstract;
          FStarC_Custard_Syntax.dt_flags = uu___1
        } in
      FStarC_Custard_Syntax.DType uu___
  | d1 -> d1
and with_modelled (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      FStarC_Custard_Syntax.DType
        {
          FStarC_Custard_Syntax.dt_name = (t.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (t.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = (t.FStarC_Custard_Syntax.dt_body);
          FStarC_Custard_Syntax.dt_flags = (FStarC_Custard_Syntax.Modelled ::
            (t.FStarC_Custard_Syntax.dt_flags))
        }
  | FStarC_Custard_Syntax.DExternal x ->
      FStarC_Custard_Syntax.DExternal
        {
          FStarC_Custard_Syntax.dx_name = (x.FStarC_Custard_Syntax.dx_name);
          FStarC_Custard_Syntax.dx_typars =
            (x.FStarC_Custard_Syntax.dx_typars);
          FStarC_Custard_Syntax.dx_ty = (x.FStarC_Custard_Syntax.dx_ty);
          FStarC_Custard_Syntax.dx_target =
            (x.FStarC_Custard_Syntax.dx_target);
          FStarC_Custard_Syntax.dx_header =
            (x.FStarC_Custard_Syntax.dx_header);
          FStarC_Custard_Syntax.dx_flags = (FStarC_Custard_Syntax.Modelled ::
            (x.FStarC_Custard_Syntax.dx_flags))
        }
  | FStarC_Custard_Syntax.DLet l ->
      FStarC_Custard_Syntax.DLet
        {
          FStarC_Custard_Syntax.dl_name = (l.FStarC_Custard_Syntax.dl_name);
          FStarC_Custard_Syntax.dl_typars =
            (l.FStarC_Custard_Syntax.dl_typars);
          FStarC_Custard_Syntax.dl_binders =
            (l.FStarC_Custard_Syntax.dl_binders);
          FStarC_Custard_Syntax.dl_ret = (l.FStarC_Custard_Syntax.dl_ret);
          FStarC_Custard_Syntax.dl_eff = (l.FStarC_Custard_Syntax.dl_eff);
          FStarC_Custard_Syntax.dl_body = (l.FStarC_Custard_Syntax.dl_body);
          FStarC_Custard_Syntax.dl_flags = (FStarC_Custard_Syntax.Modelled ::
            (l.FStarC_Custard_Syntax.dl_flags))
        }
  | d1 -> d1
and is_modelled_lid (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ =
    let uu___1 =
      FStarC_List.map FStarC_Ident.string_of_id (FStarC_Ident.ns_of_lid l) in
    FStarC_Custard_Builtins.no_fstar_stubs uu___1 in
  FStarC_Custard_Builtins.is_krml_model_name uu___
    (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid l))
and external_ty (st : state) (l : FStarC_Ident.lident)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list) :
  (Prims.string Prims.list * FStarC_Custard_Syntax.cty)=
  let uu___ = lookup_lid_typ st l in
  match uu___ with
  | FStar_Pervasives_Native.None -> ([], FStarC_Custard_Syntax.TAny)
  | FStar_Pervasives_Native.Some ((uu___1, ty), uu___2) ->
      let cs = binder_classes st l in
      let uu___3 = FStarC_Syntax_Util.arrow_formals_comp ty in
      (match uu___3 with
       | (bs, c) ->
           let tmpl_names =
             let uu___4 =
               let uu___5 =
                 FStarC_List.map
                   (fun b ->
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
                   bs in
               FStarC_List.op_At uu___5 [FStarC_Syntax_Util.comp_result c] in
             template_index_names st uu___4 in
           let rec has_runtime bs1 cs1 =
             match (bs1, cs1) with
             | ([], uu___4) -> false
             | (b::bs2, []) ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = tcenv st in
                     FStarC_Custard_Mono.is_erased_binder uu___6 b in
                   Prims.not uu___5 in
                 if uu___4 then true else has_runtime bs2 []
             | (b::bs2, c1::cs2) ->
                 if
                   (match c1 with
                    | FStarC_Custard_Mono.Poly -> true
                    | uu___4 -> false)
                 then true
                 else has_runtime bs2 cs2 in
           let has_runtime_param = has_runtime bs cs in
           let would_be_value =
             if Prims.not has_runtime_param
             then
               let uu___4 = FStarC_Syntax_Util.is_pure_or_ghost_comp c in
               Prims.not uu___4
             else false in
           let is_tmpl_index b =
             if Prims.not would_be_value
             then
               FStarC_List.existsb
                 (fun v ->
                    FStarC_Syntax_Syntax.bv_eq v
                      b.FStarC_Syntax_Syntax.binder_bv) tmpl_names
             else false in
           let rec go i bs1 cs1 subst keep anys =
             match bs1 with
             | [] -> ((FStarC_List.rev keep), subst, anys)
             | b::bs' ->
                 let cs' = match cs1 with | [] -> [] | uu___4::cs'1 -> cs'1 in
                 let cls =
                   match cs1 with
                   | [] -> FStarC_Custard_Mono.Poly
                   | c1::uu___4 -> c1 in
                 let sort =
                   FStarC_Syntax_Subst.subst subst
                     (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                 let b' =
                   {
                     FStarC_Syntax_Syntax.binder_bv =
                       (let uu___4 = b.FStarC_Syntax_Syntax.binder_bv in
                        {
                          FStarC_Syntax_Syntax.ppname =
                            (uu___4.FStarC_Syntax_Syntax.ppname);
                          FStarC_Syntax_Syntax.index =
                            (uu___4.FStarC_Syntax_Syntax.index);
                          FStarC_Syntax_Syntax.sort = sort
                        });
                     FStarC_Syntax_Syntax.binder_qual =
                       (b.FStarC_Syntax_Syntax.binder_qual);
                     FStarC_Syntax_Syntax.binder_positivity =
                       (b.FStarC_Syntax_Syntax.binder_positivity);
                     FStarC_Syntax_Syntax.binder_attrs =
                       (b.FStarC_Syntax_Syntax.binder_attrs)
                   } in
                 let uu___4 =
                   let uu___5 =
                     FStarC_List.tryFind
                       (fun uu___6 ->
                          match uu___6 with | (j, uu___7) -> j = i) margs in
                   (cls, uu___5) in
                 (match uu___4 with
                  | (FStarC_Custard_Mono.Mono, FStar_Pervasives_Native.Some
                     (uu___5, a)) when
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = tcenv st in
                          FStarC_Custard_Mono.is_type_binder uu___8 b in
                        Prims.not uu___7 in
                      if uu___6
                      then let uu___7 = is_tmpl_index b in Prims.not uu___7
                      else false ->
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_int i in
                              Prims.strcat uu___10
                                (Prims.strcat " ("
                                   (Prims.strcat
                                      (FStarC_Ident.string_of_id
                                         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                                      (Prims.strcat ") of "
                                         (Prims.strcat
                                            (FStarC_Ident.string_of_lid l)
                                            (Prims.strcat
                                               " is monomorphized, but "
                                               (Prims.strcat
                                                  (FStarC_Ident.string_of_lid
                                                     l) " is external.")))))) in
                            Prims.strcat "Custard: binder " uu___9 in
                          FStarC_Errors_Msg.text uu___8 in
                        [uu___7;
                        FStarC_Errors_Msg.text
                          "Specialization substitutes the argument into the definition's body, and an external has no body, so the argument would be discarded and the realization would never see it.";
                        FStarC_Errors_Msg.text
                          "Drop the [@@@monomorphize] annotation and pass it at runtime, or give the definition a body Custard can compile.  A monomorphized *type* argument is fine: it is substituted into the signature, which is all a type argument is.";
                        FStarC_Errors_Msg.text
                          "Or register a rule for it.  A rule replaces the call rather than specializing a body, and is handed the monomorphized argument's term, so nothing is discarded -- which is how a target intrinsic with a compile-time operand is normally expressed."] in
                      custard_error st
                        FStarC_Errors_Codes.Error_CustardMonoExternal uu___6
                  | (FStarC_Custard_Mono.Mono, FStar_Pervasives_Native.Some
                     (uu___5, a)) ->
                      go (i + Prims.int_one) bs' cs'
                        ((FStarC_Syntax_Syntax.NT
                            ((b.FStarC_Syntax_Syntax.binder_bv), a)) ::
                        subst) keep anys
                  | (FStarC_Custard_Mono.Mono, FStar_Pervasives_Native.None)
                      when
                      let uu___5 =
                        let uu___6 = tcenv st in
                        FStarC_Custard_Mono.is_type_binder uu___6 b in
                      if uu___5 then is_root st l else false ->
                      go (i + Prims.int_one) bs' cs' subst (b' :: keep) anys
                  | (FStarC_Custard_Mono.Mono, FStar_Pervasives_Native.None)
                      when
                      let uu___5 = tcenv st in
                      FStarC_Custard_Mono.is_type_binder uu___5 b ->
                      let uu___5 =
                        let uu___6 =
                          name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                        uu___6 :: anys in
                      go (i + Prims.int_one) bs' cs' subst (b' :: keep)
                        uu___5
                  | uu___5 ->
                      go (i + Prims.int_one) bs' cs' subst (b' :: keep) anys) in
           let uu___4 = go Prims.int_zero bs cs [] [] [] in
           (match uu___4 with
            | (keep, subst, anys) ->
                let c1 = FStarC_Syntax_Subst.subst_comp subst c in
                let typars =
                  FStarC_List.collect
                    (fun b ->
                       let n = name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = tcenv st in
                           FStarC_Custard_Mono.is_type_param uu___7 b in
                         if uu___6
                         then Prims.not (FStarC_List.mem n anys)
                         else false in
                       if uu___5 then [n] else []) keep in
                let res =
                  let uu___5 =
                    let uu___6 = tcenv st in
                    FStarC_Custard_Effects.result_typ uu___6 c1 in
                  ty_of_typ st uu___5 in
                let e = eff_of_comp st c1 in
                let flags =
                  let uu___5 = tcenv st in
                  let uu___6 =
                    let uu___7 = tcenv st in
                    let uu___8 = FStarC_Syntax_Util.arrow keep c1 in
                    FStarC_Custard_Mono.erased_binders uu___7 uu___8 in
                  FStarC_Custard_Mono.keep_thunk uu___5 keep c1 uu___6 in
                let vs = drop_flagged flags keep in
                let declared_erased b =
                  let t =
                    let uu___5 = tcenv st in
                    FStarC_TypeChecker_Normalize.unfold_whnf uu___5
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  let uu___5 =
                    let uu___6 = FStarC_Syntax_Subst.compress t in
                    uu___6.FStarC_Syntax_Syntax.n in
                  match uu___5 with
                  | FStarC_Syntax_Syntax.Tm_arrow uu___6 -> false
                  | uu___6 ->
                      let uu___7 = tcenv st in
                      FStarC_TypeChecker_Env.non_informative uu___7 t in
                let dropped =
                  FStarC_List.collect
                    (fun uu___5 ->
                       match uu___5 with
                       | (b, e1) ->
                           let uu___6 =
                             let uu___7 =
                               if e1
                               then
                                 let uu___8 =
                                   let uu___9 = tcenv st in
                                   FStarC_Custard_Mono.is_type_binder uu___9
                                     b in
                                 Prims.not uu___8
                               else false in
                             if uu___7
                             then
                               let uu___8 = declared_erased b in
                               Prims.not uu___8
                             else false in
                           if uu___6
                           then
                             [FStarC_Ident.string_of_id
                                (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname]
                           else []) (FStarC_List.zip keep flags) in
                (if (match dropped with | hd::tl -> true | uu___6 -> false)
                 then
                   (let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_nat
                                (FStarC_List.length dropped) in
                            Prims.strcat uu___10
                              (Prims.strcat " parameter(s) of the external "
                                 (Prims.strcat (FStarC_Ident.string_of_lid l)
                                    (Prims.strcat ": "
                                       (Prims.strcat
                                          (FStarC_String.concat ", " dropped)
                                          ".")))) in
                          Prims.strcat "Custard erased " uu___9 in
                        FStarC_Errors_Msg.text uu___8 in
                      [uu___7;
                      FStarC_Errors_Msg.text
                        "An external's prototype is fixed outside F*, so the generated call now has fewer arguments than the C declaration it is checked against.";
                      FStarC_Errors_Msg.text
                        "A pure function-typed parameter is the usual cause: [unit -> unit] is a specification and is erased, while [unit -> FStar.All.ML unit] is a computation and is kept.";
                      FStarC_Errors_Msg.text
                        "If the parameter really carries nothing, write its type as [erased t], which says so and silences this."] in
                    custard_warning st
                      FStarC_Errors_Codes.Warning_CustardExternErasure uu___6)
                 else ();
                 (let bty b =
                    let uu___6 =
                      let uu___7 = tcenv st in
                      FStarC_Custard_Mono.is_erased_binder uu___7 b in
                    if uu___6
                    then FStarC_Custard_Syntax.TUnit
                    else
                      ty_of_typ st
                        (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                  let rec build bs1 =
                    match bs1 with
                    | [] -> res
                    | b::[] ->
                        let uu___6 = let uu___7 = bty b in (uu___7, e, res) in
                        FStarC_Custard_Syntax.TArrow uu___6
                    | b::bs2 ->
                        let uu___6 =
                          let uu___7 = bty b in
                          let uu___8 = build bs2 in
                          (uu___7, FStarC_Custard_Syntax.E_Pure, uu___8) in
                        FStarC_Custard_Syntax.TArrow uu___6 in
                  let uu___6 =
                    let uu___7 =
                      FStarC_List.map
                        (fun a -> (a, FStarC_Custard_Syntax.TAny)) anys in
                    let uu___8 = build vs in
                    FStarC_Custard_Syntax.subst_cty uu___7 uu___8 in
                  (typars, uu___6)))))
and extract_sigelt (st : state) (l : FStarC_Ident.lident)
  (nm : FStarC_Custard_Syntax.name)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list)
  (n_holes : Prims.int) (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Custard_Syntax.decl=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_let
      { FStarC_Syntax_Syntax.lbs1 = (is_rec, lbs);
        FStarC_Syntax_Syntax.lids1 = uu___;_}
      ->
      let uu___1 =
        FStarC_List.tryFind
          (fun lb ->
             match lb.FStarC_Syntax_Syntax.lbname with
             | FStar_Pervasives.Inr fv ->
                 FStarC_Ident.lid_equals (FStarC_Syntax_Syntax.lid_of_fv fv)
                   l
             | FStar_Pervasives.Inl uu___2 -> false) lbs in
      (match uu___1 with
       | FStar_Pervasives_Native.Some lb ->
           let uu___2 = is_type_sig st lb.FStarC_Syntax_Syntax.lbtyp in
           if uu___2
           then
             let d =
               FStarC_Custard_Prof.timed "abbrev"
                 (fun uu___3 -> extract_type_abbrev st nm lb) in
             let uu___3 =
               let uu___4 = is_erasable st se in
               if uu___4
               then true
               else is_prop_sig st lb.FStarC_Syntax_Syntax.lbtyp in
             (if uu___3 then with_erased_flag d else d)
           else
             FStarC_Custard_Prof.timed "letbinding"
               (fun uu___3 ->
                  extract_letbinding st l nm lb is_rec margs n_holes)
       | FStar_Pervasives_Native.None ->
           FStarC_Custard_Syntax.DExternal
             {
               FStarC_Custard_Syntax.dx_name = nm;
               FStarC_Custard_Syntax.dx_typars = [];
               FStarC_Custard_Syntax.dx_ty = FStarC_Custard_Syntax.TAny;
               FStarC_Custard_Syntax.dx_target = FStar_Pervasives_Native.None;
               FStarC_Custard_Syntax.dx_header = FStar_Pervasives_Native.None;
               FStarC_Custard_Syntax.dx_flags = []
             })
  | FStarC_Syntax_Syntax.Sig_declare_typ
      { FStarC_Syntax_Syntax.lid2 = uu___; FStarC_Syntax_Syntax.us2 = uu___1;
        FStarC_Syntax_Syntax.t2 = t;_}
      ->
      let uu___2 = is_type_sig st t in
      if uu___2
      then
        let uu___3 = FStarC_Syntax_Util.arrow_formals t in
        (match uu___3 with
         | (bs, uu___4) ->
             let ps =
               FStarC_List.collect
                 (fun b ->
                    let uu___5 =
                      let uu___6 = tcenv st in
                      FStarC_Custard_Mono.is_type_param uu___6 b in
                    if uu___5
                    then
                      let uu___6 =
                        name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                      [uu___6]
                    else []) bs in
             let extern =
               let uu___5 = FStarC_Custard_Builtins.extern_type_of_lid l in
               match uu___5 with
               | FStar_Pervasives_Native.Some x ->
                   [FStarC_Custard_Syntax.Extern
                      ((x.FStarC_Custard_Builtins.x_name),
                        (x.FStarC_Custard_Builtins.x_header));
                   FStarC_Custard_Syntax.NoNewtype]
               | FStar_Pervasives_Native.None -> [] in
             let refbind =
               reference_flags l se.FStarC_Syntax_Syntax.sigattrs
                 (match extern with | hd::tl -> true | uu___5 -> false) in
             let uu___5 =
               let uu___6 =
                 let uu___7 =
                   let uu___8 =
                     let uu___9 =
                       let uu___10 = is_erasable st se in
                       if uu___10 then true else is_prop_sig st t in
                     if uu___9 then [FStarC_Custard_Syntax.Erased] else [] in
                   FStarC_List.op_At refbind uu___8 in
                 FStarC_List.op_At extern uu___7 in
               {
                 FStarC_Custard_Syntax.dt_name = nm;
                 FStarC_Custard_Syntax.dt_params = ps;
                 FStarC_Custard_Syntax.dt_body =
                   FStarC_Custard_Syntax.TAbstract;
                 FStarC_Custard_Syntax.dt_flags = uu___6
               } in
             FStarC_Custard_Syntax.DType uu___5)
      else
        (let uu___3 = assumed_projector_lb st se l t in
         match uu___3 with
         | FStar_Pervasives_Native.Some lb ->
             let uu___4 = extract_letbinding st l nm lb false margs n_holes in
             with_inline uu___4
         | FStar_Pervasives_Native.None ->
             ((let uu___5 = FStarC_Custard_Builtins.float_vocabulary_hint l in
               match uu___5 with
               | FStar_Pervasives_Native.Some want ->
                   FStarC_Errors.log_issue0
                     FStarC_Errors_Codes.Warning_CustardFloatVocabulary ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic
                        [FStarC_Errors_Msg.text
                           (Prims.strcat "Custard: "
                              (Prims.strcat (FStarC_Ident.string_of_lid l)
                                 " is declared in a floating-point module, but it is not part of the vocabulary Custard recognizes, so it becomes an external symbol."));
                        FStarC_Errors_Msg.text
                          (Prims.strcat "Did you mean to name it ["
                             (Prims.strcat want
                                "]?  Custard spells IEEE equality [ieee_eq] because [eq] does not say which equality is meant --- bitwise equality distinguishes the two zeros and makes a NaN equal to itself, and no C comparison operator does either."))])
               | FStar_Pervasives_Native.None -> ());
              (let uu___5 = external_ty st l margs in
               match uu___5 with
               | (typars, ty) ->
                   FStarC_Custard_Syntax.DExternal
                     {
                       FStarC_Custard_Syntax.dx_name = nm;
                       FStarC_Custard_Syntax.dx_typars = typars;
                       FStarC_Custard_Syntax.dx_ty = ty;
                       FStarC_Custard_Syntax.dx_target =
                         FStar_Pervasives_Native.None;
                       FStarC_Custard_Syntax.dx_header =
                         FStar_Pervasives_Native.None;
                       FStarC_Custard_Syntax.dx_flags = []
                     })))
  | FStarC_Syntax_Syntax.Sig_inductive_typ
      { FStarC_Syntax_Syntax.lid = uu___; FStarC_Syntax_Syntax.us = uu___1;
        FStarC_Syntax_Syntax.params = params;
        FStarC_Syntax_Syntax.num_uniform_params = uu___2;
        FStarC_Syntax_Syntax.t = uu___3;
        FStarC_Syntax_Syntax.mutuals = uu___4;
        FStarC_Syntax_Syntax.ds = uu___5;
        FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
      ->
      let d =
        FStarC_Custard_Prof.timed "inductive"
          (fun uu___7 -> extract_inductive st l nm params) in
      let uu___7 = is_erasable st se in
      if uu___7 then with_erased_flag d else d
  | FStarC_Syntax_Syntax.Sig_datacon uu___ ->
      FStarC_Custard_Syntax.DExternal
        {
          FStarC_Custard_Syntax.dx_name = nm;
          FStarC_Custard_Syntax.dx_typars = [];
          FStarC_Custard_Syntax.dx_ty = FStarC_Custard_Syntax.TAny;
          FStarC_Custard_Syntax.dx_target = FStar_Pervasives_Native.None;
          FStarC_Custard_Syntax.dx_header = FStar_Pervasives_Native.None;
          FStarC_Custard_Syntax.dx_flags = []
        }
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = uu___;_}
      ->
      let uu___1 =
        FStarC_List.tryFind
          (fun se1 ->
             match se1.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_inductive_typ
                 { FStarC_Syntax_Syntax.lid = lid;
                   FStarC_Syntax_Syntax.us = uu___2;
                   FStarC_Syntax_Syntax.params = uu___3;
                   FStarC_Syntax_Syntax.num_uniform_params = uu___4;
                   FStarC_Syntax_Syntax.t = uu___5;
                   FStarC_Syntax_Syntax.mutuals = uu___6;
                   FStarC_Syntax_Syntax.ds = uu___7;
                   FStarC_Syntax_Syntax.injective_type_params = uu___8;_}
                 -> FStarC_Ident.lid_equals lid l
             | uu___2 -> false) ses in
      (match uu___1 with
       | FStar_Pervasives_Native.Some se1 ->
           extract_sigelt st l nm margs n_holes se1
       | FStar_Pervasives_Native.None ->
           FStarC_Custard_Syntax.DType
             {
               FStarC_Custard_Syntax.dt_name = nm;
               FStarC_Custard_Syntax.dt_params = [];
               FStarC_Custard_Syntax.dt_body =
                 FStarC_Custard_Syntax.TAbstract;
               FStarC_Custard_Syntax.dt_flags = []
             })
  | uu___ ->
      FStarC_Custard_Syntax.DExternal
        {
          FStarC_Custard_Syntax.dx_name = nm;
          FStarC_Custard_Syntax.dx_typars = [];
          FStarC_Custard_Syntax.dx_ty = FStarC_Custard_Syntax.TAny;
          FStarC_Custard_Syntax.dx_target = FStar_Pervasives_Native.None;
          FStarC_Custard_Syntax.dx_header = FStar_Pervasives_Native.None;
          FStarC_Custard_Syntax.dx_flags = []
        }
and is_erasable (st : state) (se : FStarC_Syntax_Syntax.sigelt) : Prims.bool=
  FStarC_Syntax_Util.has_attribute se.FStarC_Syntax_Syntax.sigattrs
    FStarC_Parser_Const.erasable_attr
and with_erased_flag (d : FStarC_Custard_Syntax.decl) :
  FStarC_Custard_Syntax.decl=
  match d with
  | FStarC_Custard_Syntax.DType t ->
      FStarC_Custard_Syntax.DType
        {
          FStarC_Custard_Syntax.dt_name = (t.FStarC_Custard_Syntax.dt_name);
          FStarC_Custard_Syntax.dt_params =
            (t.FStarC_Custard_Syntax.dt_params);
          FStarC_Custard_Syntax.dt_body = (t.FStarC_Custard_Syntax.dt_body);
          FStarC_Custard_Syntax.dt_flags = (FStarC_Custard_Syntax.Erased ::
            (t.FStarC_Custard_Syntax.dt_flags))
        }
  | d1 -> d1
and is_type_sig (st : state) (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t in
  match uu___ with
  | (uu___1, c) ->
      let res =
        let uu___2 =
          FStarC_Custard_Mono.strip (FStarC_Syntax_Util.comp_result c) in
        sig_head_norm st uu___2 in
      let rec is_type t1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Subst.compress t1 in
          uu___3.FStarC_Syntax_Syntax.n in
        match uu___2 with
        | FStarC_Syntax_Syntax.Tm_type uu___3 -> true
        | FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b2 = b;
              FStarC_Syntax_Syntax.phi = uu___3;_}
            ->
            let uu___4 = sig_head_norm st b.FStarC_Syntax_Syntax.sort in
            is_type uu___4
        | FStarC_Syntax_Syntax.Tm_fvar fv ->
            FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.prop_lid
        | uu___3 -> false in
      is_type res
and sig_head_norm (st : state) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  norm_bounded st "a type signature"
    [FStarC_TypeChecker_Env.Weak;
    FStarC_TypeChecker_Env.HNF;
    FStarC_TypeChecker_Env.AllowUnboundUniverses;
    FStarC_TypeChecker_Env.EraseUniverses;
    FStarC_TypeChecker_Env.Beta;
    FStarC_TypeChecker_Env.Iota;
    FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant] t
and is_prop_sig (st : state) (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t in
  match uu___ with
  | (uu___1, c) ->
      let res =
        let uu___2 =
          FStarC_Custard_Mono.strip (FStarC_Syntax_Util.comp_result c) in
        sig_head_norm st uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Custard_Mono.strip res in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.prop_lid
       | uu___3 -> false)
and extract_type_abbrev (st : state) (nm : FStarC_Custard_Syntax.name)
  (lb : FStarC_Syntax_Syntax.letbinding) : FStarC_Custard_Syntax.decl=
  let uu___ = FStarC_Syntax_Util.abs_formals lb.FStarC_Syntax_Syntax.lbdef in
  match uu___ with
  | (bs, body, uu___1) ->
      let uu___2 =
        let uu___3 =
          FStarC_Syntax_Util.arrow_formals lb.FStarC_Syntax_Syntax.lbtyp in
        match uu___3 with
        | (kbs, uu___4) ->
            let n = (FStarC_List.length kbs) - (FStarC_List.length bs) in
            if n <= Prims.int_zero
            then (bs, body)
            else
              (let extra =
                 FStarC_List.map
                   (fun b ->
                      let uu___5 =
                        FStarC_Syntax_Syntax.new_bv
                          FStar_Pervasives_Native.None
                          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                      FStarC_Syntax_Syntax.mk_binder uu___5)
                   (FStar_Pervasives_Native.snd
                      (FStarC_List.splitAt ((FStarC_List.length kbs) - n) kbs)) in
               let args =
                 FStarC_List.map
                   (fun b ->
                      let uu___5 =
                        FStarC_Syntax_Syntax.bv_to_name
                          b.FStarC_Syntax_Syntax.binder_bv in
                      FStarC_Syntax_Syntax.as_arg uu___5) extra in
               let uu___5 = FStarC_Syntax_Util.mk_app body args in
               ((FStarC_List.op_At bs extra), uu___5)) in
      (match uu___2 with
       | (bs1, body1) ->
           let uu___3 =
             let uu___4 =
               FStarC_List.collect
                 (fun b ->
                    let uu___5 =
                      let uu___6 = tcenv st in
                      FStarC_Custard_Mono.is_type_param uu___6 b in
                    if uu___5
                    then
                      let uu___6 =
                        name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                      [uu___6]
                    else []) bs1 in
             let uu___5 =
               let uu___6 = ty_of_typ st body1 in
               FStarC_Custard_Syntax.TAbbrev uu___6 in
             {
               FStarC_Custard_Syntax.dt_name = nm;
               FStarC_Custard_Syntax.dt_params = uu___4;
               FStarC_Custard_Syntax.dt_body = uu___5;
               FStarC_Custard_Syntax.dt_flags = []
             } in
           FStarC_Custard_Syntax.DType uu___3)
and eta_safe (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.unascribe t in
      FStarC_Syntax_Subst.compress uu___2 in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_abs uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_name uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_bvar uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_constant uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_uinst uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_arrow uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = tm; FStarC_Syntax_Syntax.meta = uu___1;_}
      -> eta_safe tm
  | uu___1 -> false
and specialize (st : state) (ty : FStarC_Syntax_Syntax.typ)
  (def : FStarC_Syntax_Syntax.term)
  (cs : FStarC_Custard_Mono.bclass Prims.list)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list)
  (n_holes : Prims.int) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
    FStarC_Custard_Mono.bclass Prims.list * FStarC_Syntax_Syntax.binders)=
  let uu___ =
    match margs with
    | (uu___1, a0)::uu___2 when n_holes > Prims.int_zero ->
        let uu___3 = FStarC_Syntax_Util.abs_formals a0 in
        (match uu___3 with
         | (bs0, uu___4, uu___5) ->
             let hbs =
               FStarC_List.map
                 (fun b ->
                    let uu___6 =
                      FStarC_Syntax_Syntax.new_bv
                        FStar_Pervasives_Native.None
                        (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                    FStarC_Syntax_Syntax.mk_binder uu___6)
                 (FStar_Pervasives_Native.fst
                    (FStarC_List.splitAt n_holes bs0)) in
             let hargs =
               FStarC_List.map
                 (fun b ->
                    let uu___6 =
                      FStarC_Syntax_Syntax.bv_to_name
                        b.FStarC_Syntax_Syntax.binder_bv in
                    FStarC_Syntax_Syntax.as_arg uu___6) hbs in
             let inst t =
               let uu___6 = FStarC_Syntax_Util.mk_app t hargs in
               norm_bounded st "a monomorphized argument"
                 [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                 FStarC_TypeChecker_Env.Beta] uu___6 in
             let uu___6 =
               FStarC_List.map
                 (fun uu___7 ->
                    match uu___7 with
                    | (i, t) -> let uu___8 = inst t in (i, uu___8)) margs in
             (hbs, uu___6))
    | uu___1 -> ([], margs) in
  match uu___ with
  | (hbs, margs1) ->
      let uu___1 =
        let uu___2 = tcenv st in
        FStarC_Custard_Mono.arrow_formals_unfold uu___2 ty in
      (match uu___1 with
       | (bs, c) ->
           let cut =
             let base =
               let uu___2 = eta_safe def in
               if uu___2
               then
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Util.arrow_formals_comp ty in
                   FStar_Pervasives_Native.fst uu___4 in
                 FStarC_List.length uu___3
               else
                 (let uu___3 = FStarC_Syntax_Util.abs_formals def in
                  match uu___3 with
                  | (dbs, uu___4, uu___5) -> FStarC_List.length dbs) in
             FStarC_List.fold_left
               (fun n uu___2 ->
                  match uu___2 with
                  | (j, uu___3) ->
                      if (j + Prims.int_one) > n
                      then j + Prims.int_one
                      else n) base margs1 in
           ((let uu___3 = FStarC_Options.custard_dump_specializations () in
             if uu___3
             then
               let folded =
                 let uu___4 =
                   let uu___5 = FStarC_Syntax_Util.arrow_formals_comp ty in
                   FStar_Pervasives_Native.fst uu___5 in
                 FStarC_List.length uu___4 in
               ((let uu___5 =
                   let uu___6 = FStarC_Effect.op_Bang st.cur in
                   FStarC_Custard_Syntax.string_of_name uu___6 in
                 let uu___6 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                     folded in
                 let uu___7 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                     (FStarC_List.length bs) in
                 let uu___8 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int cut in
                 let uu___9 =
                   let uu___10 = eta_safe def in
                   FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                     uu___10 in
                 FStarC_Format.print5
                   "Custard: arity of %s: folded=%s unfolded=%s cut=%s eta_safe=%s\n"
                   uu___5 uu___6 uu___7 uu___8 uu___9);
                (let uu___5 =
                   let uu___6 = tcenv st in
                   FStarC_Custard_Mono.classes_to_string uu___6 bs cs in
                 let uu___6 =
                   let uu___7 =
                     FStarC_List.map
                       (fun uu___8 ->
                          match uu___8 with
                          | (j, uu___9) ->
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_int j) margs1 in
                   FStarC_String.concat "; " uu___7 in
                 FStarC_Format.print2 "  classes=[%s] mono_args=[%s]\n"
                   uu___5 uu___6))
             else ());
            (let rec go i bs1 cs1 subst spine poly polycs =
               match bs1 with
               | [] ->
                   let uu___3 = FStarC_Syntax_Subst.subst_comp subst c in
                   ((FStarC_List.rev spine), (FStarC_List.rev poly),
                     (FStarC_List.rev polycs), uu___3)
               | uu___3::uu___4 when i >= cut ->
                   let uu___5 =
                     let uu___6 =
                       let uu___7 =
                         FStarC_Syntax_Subst.subst_binders subst bs1 in
                       let uu___8 = FStarC_Syntax_Subst.subst_comp subst c in
                       FStarC_Syntax_Util.arrow uu___7 uu___8 in
                     FStarC_Syntax_Syntax.mk_Total uu___6 in
                   ((FStarC_List.rev spine), (FStarC_List.rev poly),
                     (FStarC_List.rev polycs), uu___5)
               | b::bs' ->
                   let uu___3 =
                     match cs1 with
                     | [] -> (FStarC_Custard_Mono.Poly, [])
                     | c1::cs' -> (c1, cs') in
                   (match uu___3 with
                    | (cls, cs') ->
                        let sort =
                          FStarC_Syntax_Subst.subst subst
                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        let marg =
                          FStarC_List.tryFind
                            (fun uu___4 ->
                               match uu___4 with | (j, uu___5) -> j = i)
                            margs1 in
                        (match (cls, marg) with
                         | (FStarC_Custard_Mono.Mono,
                            FStar_Pervasives_Native.Some (uu___4, a)) ->
                             go (i + Prims.int_one) bs' cs'
                               ((FStarC_Syntax_Syntax.NT
                                   ((b.FStarC_Syntax_Syntax.binder_bv), a))
                               :: subst)
                               ((a, (FStarC_Syntax_Util.aqual_of_binder b))
                               :: spine) poly polycs
                         | uu___4 ->
                             let bv =
                               let uu___5 = b.FStarC_Syntax_Syntax.binder_bv in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (uu___5.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (uu___5.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = sort
                               } in
                             let b' =
                               {
                                 FStarC_Syntax_Syntax.binder_bv = bv;
                                 FStarC_Syntax_Syntax.binder_qual =
                                   (b.FStarC_Syntax_Syntax.binder_qual);
                                 FStarC_Syntax_Syntax.binder_positivity =
                                   (b.FStarC_Syntax_Syntax.binder_positivity);
                                 FStarC_Syntax_Syntax.binder_attrs =
                                   (b.FStarC_Syntax_Syntax.binder_attrs)
                               } in
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStarC_Syntax_Syntax.bv_to_name bv in
                                 (uu___7,
                                   (FStarC_Syntax_Util.aqual_of_binder b)) in
                               uu___6 :: spine in
                             go (i + Prims.int_one) bs' cs' subst uu___5 (b'
                               :: poly) (cls :: polycs))) in
             let uu___3 = go Prims.int_zero bs cs [] [] [] [] in
             match uu___3 with
             | (spine, poly, polycs, c1) ->
                 ((let uu___5 =
                     FStarC_Options.custard_dump_specializations () in
                   if uu___5
                   then
                     let uu___6 =
                       FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                         (FStarC_List.length poly) in
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStarC_List.filter
                             FStarC_Custard_Mono.uu___is_Dropped polycs in
                         FStarC_List.length uu___9 in
                       FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                         uu___8 in
                     let uu___8 =
                       FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                         (FStarC_List.length spine) in
                     FStarC_Format.print3
                       "  abstracted %s parameters of which %s dropped, %s in the spine\n"
                       uu___6 uu___7 uu___8
                   else ());
                  (let poly1 = FStarC_List.op_At hbs poly in
                   let polycs1 =
                     let uu___5 =
                       FStarC_List.map
                         (fun uu___6 -> FStarC_Custard_Mono.Poly) hbs in
                     FStarC_List.op_At uu___5 polycs in
                   let applied =
                     match spine with
                     | [] -> def
                     | uu___5 -> FStarC_Syntax_Util.mk_app def spine in
                   let benv =
                     let uu___5 = tcenv st in
                     FStarC_TypeChecker_Env.push_binders uu___5 poly1 in
                   let extra =
                     let uu___5 = type_matched_heads benv applied in
                     match uu___5 with
                     | [] -> FStar_Pervasives_Native.None
                     | lids ->
                         let steps =
                           FStarC_List.filter
                             (fun s ->
                                match s with
                                | FStarC_TypeChecker_Env.Exclude
                                    (FStarC_TypeChecker_Env.Zeta) -> false
                                | uu___6 -> true) custard_norm_steps in
                         norm_optional_in benv
                           (FStarC_List.op_At steps
                              [FStarC_TypeChecker_Env.Zeta;
                              FStarC_TypeChecker_Env.UnfoldUntil
                                FStarC_Syntax_Syntax.delta_constant;
                              FStarC_TypeChecker_Env.UnfoldOnly lids])
                           applied in
                   let body =
                     match extra with
                     | FStar_Pervasives_Native.Some b -> b
                     | FStar_Pervasives_Native.None ->
                         norm_bounded_in st benv "a definition body"
                           custard_norm_steps applied in
                   let uu___5 =
                     FStarC_Syntax_Util.abs poly1 body
                       FStar_Pervasives_Native.None in
                   (uu___5, c1, polycs1, poly1))))))
and extract_letbinding (st : state) (l : FStarC_Ident.lident)
  (nm : FStarC_Custard_Syntax.name) (lb : FStarC_Syntax_Syntax.letbinding)
  (is_rec : Prims.bool)
  (margs : (Prims.int * FStarC_Syntax_Syntax.term) Prims.list)
  (n_holes : Prims.int) : FStarC_Custard_Syntax.decl=
  let cs = binder_classes st l in
  let src_attrs =
    let uu___ =
      let uu___1 =
        let uu___2 = tcenv st in
        FStarC_TypeChecker_Env.lookup_sigelt uu___2 l in
      match uu___1 with
      | FStar_Pervasives_Native.Some se -> se.FStarC_Syntax_Syntax.sigattrs
      | FStar_Pervasives_Native.None -> [] in
    FStarC_List.op_At lb.FStarC_Syntax_Syntax.lbattrs uu___ in
  let saved_cur = FStarC_Effect.op_Bang st.cur in
  let saved_cur_lid = FStarC_Effect.op_Bang st.cur_lid in
  FStarC_Effect.op_Colon_Equals st.cur nm;
  FStarC_Effect.op_Colon_Equals st.cur_lid (FStar_Pervasives_Native.Some l);
  (let uu___2 =
     FStarC_Custard_Prof.timed "specialize"
       (fun uu___3 ->
          specialize st lb.FStarC_Syntax_Syntax.lbtyp
            lb.FStarC_Syntax_Syntax.lbdef cs margs n_holes) in
   match uu___2 with
   | (def, c, polycs, poly) ->
       let uu___3 = FStarC_Syntax_Util.abs_formals def in
       (match uu___3 with
        | (bs, body, rc) ->
            (FStarC_List.iter
               (fun b ->
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.index in
                  FStarC_SMap.add st.defbinders uu___5 ()) bs;
             (let rec realign ps bs1 =
                match (ps, bs1) with
                | (p::ps1, b::bs2) ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStarC_Syntax_Syntax.bv_to_name
                            b.FStarC_Syntax_Syntax.binder_bv in
                        ((p.FStarC_Syntax_Syntax.binder_bv), uu___7) in
                      FStarC_Syntax_Syntax.NT uu___6 in
                    let uu___6 = realign ps1 bs2 in uu___5 :: uu___6
                | uu___5 -> [] in
              let c1 =
                let uu___5 = realign poly bs in
                FStarC_Syntax_Subst.subst_comp uu___5 c in
              let nth_class i =
                let rec go cs1 i1 =
                  match cs1 with
                  | [] -> false
                  | c2::cs2 ->
                      if i1 <= Prims.int_zero
                      then
                        (match c2 with
                         | FStarC_Custard_Mono.Dropped -> true
                         | uu___5 -> false)
                      else go cs2 (i1 - Prims.int_one) in
                go polycs i in
              let n_poly = FStarC_List.length polycs in
              let n_cs = FStarC_List.length cs in
              let cs_class i =
                let j = i - n_holes in
                if (j >= Prims.int_zero) && (j < n_cs)
                then FStar_Pervasives_Native.Some (FStarC_List.nth cs j)
                else FStar_Pervasives_Native.None in
              let flags =
                FStarC_List.mapi
                  (fun i b ->
                     let uu___5 = nth_class i in
                     if uu___5
                     then true
                     else
                       if i >= n_poly
                       then
                         (let uu___6 = cs_class i in
                          match uu___6 with
                          | FStar_Pervasives_Native.Some c2 ->
                              (match c2 with
                               | FStarC_Custard_Mono.Dropped -> true
                               | uu___7 -> false)
                          | FStar_Pervasives_Native.None ->
                              let uu___7 = tcenv st in
                              FStarC_Custard_Mono.is_erased_binder uu___7 b)
                       else false) bs in
              let n_extra =
                let n = (FStarC_List.length bs) - n_poly in
                if n > Prims.int_zero then n else Prims.int_zero in
              let typars =
                FStarC_List.collect
                  (fun b ->
                     let uu___5 =
                       let uu___6 = tcenv st in
                       FStarC_Custard_Mono.is_type_param uu___6 b in
                     if uu___5
                     then
                       let uu___6 =
                         name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                       [uu___6]
                     else []) bs in
              let benv =
                FStarC_Custard_Prof.timed "push_binders"
                  (fun uu___5 ->
                     let uu___6 = tcenv st in
                     FStarC_TypeChecker_Env.push_binders uu___6 bs) in
              let bs1 = drop_flagged flags bs in
              let binders =
                FStarC_List.map
                  (fun b ->
                     let uu___5 = name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 = tcenv st in
                         FStarC_Custard_Mono.is_erased_binder uu___8 b in
                       if uu___7
                       then FStarC_Custard_Syntax.TUnit
                       else
                         ty_of_typ st
                           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                     {
                       FStarC_Custard_Syntax.b_name = uu___5;
                       FStarC_Custard_Syntax.b_ty = uu___6
                     }) bs1 in
              (let uu___6 = FStarC_Options.custard_dump_specializations () in
               if uu___6
               then
                 let uu___7 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                     (FStarC_List.length binders) in
                 let uu___8 =
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int
                     (let n = ((FStarC_List.length bs1) - n_cs) + n_holes in
                      if n > Prims.int_zero then n else Prims.int_zero) in
                 FStarC_Format.print2
                   "  emitted %s parameters (%s lambdas past the classification)\n"
                   uu___7 uu___8
               else ());
              (let rec peel n e t =
                 if n <= Prims.int_zero
                 then (e, t)
                 else
                   (let uu___6 = head_ty st t (Prims.of_int 10) in
                    match uu___6 with
                    | FStarC_Custard_Syntax.TArrow (uu___7, e', r) ->
                        peel (n - Prims.int_one) e' r
                    | uu___7 -> (e, t)) in
               let rec peel_typ n e t =
                 if n <= Prims.int_zero
                 then let uu___6 = ty_of_typ st t in (e, uu___6)
                 else
                   (let t1 =
                      norm_bounded_in st benv "a result type"
                        [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                        FStarC_TypeChecker_Env.Beta;
                        FStarC_TypeChecker_Env.Weak;
                        FStarC_TypeChecker_Env.HNF;
                        FStarC_TypeChecker_Env.UnfoldUntil
                          FStarC_Syntax_Syntax.delta_constant] t in
                    let t2 = FStarC_Custard_Mono.strip t1 in
                    match t2.FStarC_Syntax_Syntax.n with
                    | FStarC_Syntax_Syntax.Tm_arrow uu___6 ->
                        let uu___7 = FStarC_Syntax_Util.arrow_formals_comp t2 in
                        (match uu___7 with
                         | (bs2, c') ->
                             let k = FStarC_List.length bs2 in
                             if k > n
                             then
                               let uu___8 =
                                 let uu___9 =
                                   FStarC_Syntax_Util.arrow
                                     (FStar_Pervasives_Native.snd
                                        (FStarC_List.splitAt n bs2)) c' in
                                 ty_of_typ st uu___9 in
                               (FStarC_Custard_Syntax.E_Pure, uu___8)
                             else
                               (let uu___8 =
                                  if k = n
                                  then
                                    let uu___9 = tcenv st in
                                    FStarC_Custard_Effects.is_erasable uu___9
                                      c'
                                  else false in
                                if uu___8
                                then
                                  (FStarC_Custard_Syntax.E_Ghost,
                                    FStarC_Custard_Syntax.TUnit)
                                else
                                  (let uu___9 =
                                     if k = n
                                     then
                                       let uu___10 = tcenv st in
                                       FStarC_Custard_Effects.is_reifiable
                                         uu___10
                                         (FStarC_Syntax_Util.comp_effect_name
                                            c')
                                     else false in
                                   if uu___9
                                   then
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 = env_for_comp benv c' in
                                         FStarC_Custard_Effects.reify_comp
                                           uu___12 c' in
                                       ty_of_typ st uu___11 in
                                     (FStarC_Custard_Syntax.E_Pure, uu___10)
                                   else
                                     (let uu___10 = eff_of_comp st c' in
                                      let uu___11 =
                                        let uu___12 = tcenv st in
                                        FStarC_Custard_Effects.result_typ
                                          uu___12 c' in
                                      peel_typ (n - k) uu___10 uu___11))))
                    | uu___6 ->
                        let uu___7 =
                          let uu___8 = ty_of_typ st t2 in
                          head_ty st uu___8 (Prims.of_int 10) in
                        peel n e uu___7) in
               let res_typ =
                 let uu___6 = tcenv st in
                 FStarC_Custard_Effects.result_typ uu___6 c1 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = tcenv st in
                   FStarC_Custard_Effects.is_erasable uu___8 c1 in
                 if uu___7
                 then
                   (FStarC_Custard_Syntax.E_Ghost,
                     FStarC_Custard_Syntax.TUnit)
                 else
                   (let uu___8 =
                      let uu___9 = tcenv st in
                      FStarC_Custard_Effects.is_reifiable uu___9
                        (FStarC_Syntax_Util.comp_effect_name c1) in
                    if uu___8
                    then
                      let uu___9 =
                        let uu___10 =
                          let uu___11 = env_for_comp benv c1 in
                          FStarC_Custard_Effects.reify_comp uu___11 c1 in
                        ty_of_typ st uu___10 in
                      peel n_extra FStarC_Custard_Syntax.E_Pure uu___9
                    else
                      (let uu___9 = eff_of_comp st c1 in
                       peel_typ n_extra uu___9 res_typ)) in
               match uu___6 with
               | (eff, ret) ->
                   let body1 =
                     FStarC_Custard_Prof.timed "reify"
                       (fun uu___7 ->
                          match rc with
                          | FStar_Pervasives_Native.Some rc1 ->
                              let uu___8 = env_for_term benv body in
                              FStarC_Custard_Effects.maybe_reify uu___8 body
                                rc1.FStarC_Syntax_Syntax.residual_effect
                          | FStar_Pervasives_Native.None ->
                              let uu___8 = env_for_term benv body in
                              FStarC_Custard_Effects.maybe_reify uu___8 body
                                (FStarC_Syntax_Util.comp_effect_name c1)) in
                   ((let uu___8 = FStarC_Effect.op_Bang st.chain in
                     match uu___8 with
                     | key::uu___9 ->
                         FStarC_SMap.add st.emitted key
                           (FStarC_Custard_Syntax.DLet
                              {
                                FStarC_Custard_Syntax.dl_name = nm;
                                FStarC_Custard_Syntax.dl_typars = typars;
                                FStarC_Custard_Syntax.dl_binders = binders;
                                FStarC_Custard_Syntax.dl_ret = ret;
                                FStarC_Custard_Syntax.dl_eff = eff;
                                FStarC_Custard_Syntax.dl_body =
                                  (FStarC_Custard_Syntax.mk
                                     (FStarC_Custard_Syntax.EAbort
                                        "Custard: provisional body") ret eff);
                                FStarC_Custard_Syntax.dl_flags = []
                              })
                     | [] -> ());
                    (match () with
                     | () ->
                         let dl_body = expr_of_term st body1 in
                         (FStarC_Effect.op_Colon_Equals st.cur saved_cur;
                          FStarC_Effect.op_Colon_Equals st.cur_lid
                            saved_cur_lid;
                          (let uu___10 =
                             let uu___11 =
                               let uu___12 = c_decoration_flags src_attrs in
                               FStarC_List.op_At
                                 (if is_rec
                                  then [FStarC_Custard_Syntax.Rec [nm]]
                                  else []) uu___12 in
                             {
                               FStarC_Custard_Syntax.dl_name = nm;
                               FStarC_Custard_Syntax.dl_typars = typars;
                               FStarC_Custard_Syntax.dl_binders = binders;
                               FStarC_Custard_Syntax.dl_ret = ret;
                               FStarC_Custard_Syntax.dl_eff = eff;
                               FStarC_Custard_Syntax.dl_body = dl_body;
                               FStarC_Custard_Syntax.dl_flags = uu___11
                             } in
                           FStarC_Custard_Syntax.DLet uu___10)))))))))
and is_tuple_name (n : FStarC_Custard_Syntax.name) : Prims.bool=
  (n.FStarC_Custard_Syntax.ns = ["FStar"; "Pervasives"; "Native"]) &&
    (FStarC_Util.starts_with n.FStarC_Custard_Syntax.id "tuple")
and field_ty (st : state) (b : FStarC_Syntax_Syntax.binder) :
  FStarC_Custard_Syntax.cty=
  let t =
    ty_of_typ st (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
  let asked =
    FStarC_Syntax_Util.has_attribute b.FStarC_Syntax_Syntax.binder_attrs
      FStarC_Parser_Const.custard_inline_field_attr in
  match t with
  | FStarC_Custard_Syntax.TApp (n, uu___) when asked || (is_tuple_name n) ->
      FStarC_Custard_Syntax.TInline t
  | uu___ -> t
and extract_inductive (st : state) (l : FStarC_Ident.lident)
  (nm : FStarC_Custard_Syntax.name) (params : FStarC_Syntax_Syntax.binders) :
  FStarC_Custard_Syntax.decl=
  let params1 = FStarC_Syntax_Subst.open_binders params in
  let uu___ =
    let uu___1 = tcenv st in FStarC_TypeChecker_Env.datacons_of_typ uu___1 l in
  match uu___ with
  | (uu___1, ctors) ->
      let n_params = FStarC_List.length params1 in
      let ty_params =
        FStarC_List.collect
          (fun b ->
             let uu___2 = keeps_param st l b in
             if uu___2
             then
               let uu___3 = name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
               [uu___3]
             else []) params1 in
      let ctor c =
        let uu___2 =
          let uu___3 = tcenv st in
          FStarC_TypeChecker_Env.lookup_datacon uu___3 c in
        match uu___2 with
        | (uu___3, ty) ->
            let uu___4 = FStarC_Syntax_Util.arrow_formals_comp ty in
            (match uu___4 with
             | (bs, uu___5) ->
                 let bs1 =
                   if (FStarC_List.length bs) >= n_params
                   then
                     let uu___6 = FStarC_List.splitAt n_params bs in
                     match uu___6 with
                     | (pre, bs2) ->
                         let subst =
                           FStarC_List.map2
                             (fun pb b ->
                                let uu___7 =
                                  let uu___8 =
                                    FStarC_Syntax_Syntax.bv_to_name
                                      b.FStarC_Syntax_Syntax.binder_bv in
                                  ((pb.FStarC_Syntax_Syntax.binder_bv),
                                    uu___8) in
                                FStarC_Syntax_Syntax.NT uu___7) pre params1 in
                         FStarC_Syntax_Subst.subst_binders subst bs2
                   else bs in
                 (FStarC_List.iter
                    (fun b ->
                       check_binder_attrs "the field"
                         (FStarC_Ident.string_of_lid c) b;
                       (let uu___8 =
                          FStarC_Syntax_Util.has_attribute
                            b.FStarC_Syntax_Syntax.binder_attrs
                            FStarC_Parser_Const.monomorphize_attr in
                        if uu___8
                        then
                          FStarC_Errors.log_issue0
                            FStarC_Errors_Codes.Warning_CustardIneffectiveAttribute
                            ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_list_doc)
                            (Obj.magic
                               [FStarC_Errors_Msg.text
                                  (Prims.strcat
                                     "[@@monomorphize] on the field "
                                     (Prims.strcat
                                        (FStarC_Ident.string_of_id
                                           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                                        (Prims.strcat " of "
                                           (Prims.strcat
                                              (FStarC_Ident.string_of_lid c)
                                              " has no effect."))));
                               FStarC_Errors_Msg.text
                                 "The attribute selects which *arguments of a function* are known at specialization time (section 3.2).  A constructor field is not an argument of anything, so there is no call site at which a value for it could be known, and nothing reads the attribute.";
                               FStarC_Errors_Msg.text
                                 "A field of kind Type0 whose siblings' types mention it makes the type an existential package rather than an instance of a parameterized type, which section 30.3 records as unsupported. There is no annotation that changes that."])
                        else ())) bs1;
                  (let bs2 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 = tcenv st in
                         FStarC_Custard_Mono.is_erased_binder uu___9 in
                       FStarC_List.map uu___8 bs1 in
                     drop_flagged uu___7 bs1 in
                   let uu___7 = name_of_lid c in
                   let uu___8 =
                     FStarC_List.map
                       (fun b ->
                          let uu___9 =
                            name_of_bv b.FStarC_Syntax_Syntax.binder_bv in
                          let uu___10 = field_ty st b in (uu___9, uu___10))
                       bs2 in
                   (uu___7, uu___8)))) in
      let is_record =
        let uu___2 =
          let uu___3 = tcenv st in
          FStarC_TypeChecker_Env.lookup_sigelt uu___3 l in
        match uu___2 with
        | FStar_Pervasives_Native.Some se ->
            FStarC_List.existsb
              (fun q ->
                 match q with
                 | FStarC_Syntax_Syntax.RecordType _0 -> true
                 | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals
        | FStar_Pervasives_Native.None -> false in
      let existential =
        let uu___2 =
          let uu___3 = tcenv st in
          FStarC_Custard_Mono.existential_of_lid uu___3 l in
        match uu___2 with
        | FStar_Pervasives_Native.Some (c, f) ->
            [FStarC_Custard_Syntax.Existential
               ((FStarC_Ident.string_of_lid c),
                 (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid f)))]
        | FStar_Pervasives_Native.None -> [] in
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_List.map ctor ctors in
          FStarC_Custard_Syntax.TVariant uu___4 in
        {
          FStarC_Custard_Syntax.dt_name = nm;
          FStarC_Custard_Syntax.dt_params = ty_params;
          FStarC_Custard_Syntax.dt_body = uu___3;
          FStarC_Custard_Syntax.dt_flags =
            (FStarC_List.op_At
               (if is_record
                then [FStarC_Custard_Syntax.SourceRecord]
                else []) existential)
        } in
      FStarC_Custard_Syntax.DType uu___2
let dump_specializations (st : state) : unit=
  FStarC_Format.print_string "Custard specializations:\n";
  FStarC_SMap.iter st.counts
    (fun l n ->
       if n > Prims.int_one
       then
         let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
         FStarC_Format.print2 "  %s -> %s\n" l uu___2
       else ());
  (let uu___2 =
     let uu___3 =
       FStarC_SMap.fold st.counts (fun uu___4 n acc -> acc + n)
         Prims.int_zero in
     FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
   FStarC_Format.print1 "  (total: %s)\n" uu___2)
let install_chain_reporter (st : state) : unit=
  FStarC_Effect.op_Colon_Equals FStarC_Custard_Mono.chain_reporter
    (fun uu___ -> request_chain st)
let erased_definition (st : state) (ty : FStarC_Syntax_Syntax.typ) :
  Prims.bool=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp ty in
  match uu___ with
  | (uu___1, c) ->
      if
        FStarC_Syntax_Util.is_ghost_effect
          (FStarC_Syntax_Util.comp_effect_name c)
      then true
      else
        (let uu___2 = tcenv st in
         FStarC_TypeChecker_Util.must_erase_for_extraction uu___2
           (FStarC_Syntax_Util.comp_result c))
let unrootable_definition (st : state) (ty : FStarC_Syntax_Syntax.typ) :
  Prims.bool=
  let uu___ =
    let uu___1 = tcenv st in FStarC_Custard_Mono.type_binders uu___1 ty in
  FStarC_List.existsb (fun b -> b) uu___
let root_is_erased (st : state) (l : FStarC_Ident.lident) : Prims.bool=
  let contentless ty =
    let uu___ = FStarC_Syntax_Util.arrow_formals_comp ty in
    match uu___ with
    | (uu___1, c) ->
        let uu___2 = let uu___3 = is_type_sig st ty in Prims.not uu___3 in
        if uu___2
        then
          (if
             FStarC_Syntax_Util.is_ghost_effect
               (FStarC_Syntax_Util.comp_effect_name c)
           then true
           else
             (let uu___3 = FStarC_Syntax_Util.is_pure_or_ghost_comp c in
              if uu___3
              then
                let uu___4 = tcenv st in
                FStarC_TypeChecker_Util.must_erase_for_extraction uu___4
                  (FStarC_Syntax_Util.comp_result c)
              else false))
        else false in
  let uu___ = lookup_lid_typ st l in
  match uu___ with
  | FStar_Pervasives_Native.Some ((uu___1, ty), uu___2) when contentless ty
      ->
      (FStarC_Errors.log_issue0
         FStarC_Errors_Codes.Error_CustardEntryNotFound ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic
            [FStarC_Errors_Msg.text
               (Prims.strcat "Custard entry point "
                  (Prims.strcat (FStarC_Ident.string_of_lid l)
                     " is a specification, not code."));
            FStarC_Errors_Msg.text
              "Its result type is erased -- ghost, prop, slprop or squash -- so there is nothing to extract from it.";
            FStarC_Errors_Msg.text
              "Name the function that uses it instead, or use --custard_entry_module, which skips specifications."]);
       true)
  | uu___1 -> false
let noextract_to_this_backend (se : FStarC_Syntax_Syntax.sigelt) :
  Prims.bool=
  let b = FStarC_Options.custard_backend () in
  let names = "Custard" :: b ::
    (if ((b = "KrmlC") || (b = "KrmlRust")) || (b = "C")
     then ["krml"; "Krml"]
     else []) in
  FStarC_List.existsb
    (fun attr ->
       let uu___ = FStarC_Syntax_Util.head_and_args_full attr in
       match uu___ with
       | (hd, args) ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress hd in
               uu___3.FStarC_Syntax_Syntax.n in
             (uu___2, args) in
           (match uu___1 with
            | (FStarC_Syntax_Syntax.Tm_fvar fv, (a, uu___2)::[]) when
                FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.noextract_to_attr
                ->
                let uu___3 =
                  FStarC_Syntax_Embeddings_Base.try_unembed
                    FStarC_Syntax_Embeddings.e_string a
                    FStarC_Syntax_Embeddings_Base.id_norm_cb in
                (match uu___3 with
                 | FStar_Pervasives_Native.Some s ->
                     let s1 = s in FStarC_List.contains s1 names
                 | FStar_Pervasives_Native.None -> false)
            | uu___2 -> false)) se.FStarC_Syntax_Syntax.sigattrs
let run (st : state) (roots : FStarC_Ident.lident Prims.list)
  (main : FStarC_Ident.lident FStar_Pervasives_Native.option)
  (per_module : FStarC_Syntax_Syntax.modul -> unit) :
  FStarC_Custard_Syntax.program=
  let mark' quiet f l =
    let key =
      string_of_key
        { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = Prims.int_zero
        } in
    let uu___ =
      request st
        { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = Prims.int_zero
        } in
    let uu___1 = FStarC_SMap.try_find st.emitted key in
    match uu___1 with
    | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DLet d) ->
        FStarC_SMap.add st.emitted key
          (FStarC_Custard_Syntax.DLet
             {
               FStarC_Custard_Syntax.dl_name =
                 (d.FStarC_Custard_Syntax.dl_name);
               FStarC_Custard_Syntax.dl_typars =
                 (d.FStarC_Custard_Syntax.dl_typars);
               FStarC_Custard_Syntax.dl_binders =
                 (d.FStarC_Custard_Syntax.dl_binders);
               FStarC_Custard_Syntax.dl_ret =
                 (d.FStarC_Custard_Syntax.dl_ret);
               FStarC_Custard_Syntax.dl_eff =
                 (d.FStarC_Custard_Syntax.dl_eff);
               FStarC_Custard_Syntax.dl_body =
                 (d.FStarC_Custard_Syntax.dl_body);
               FStarC_Custard_Syntax.dl_flags = (f ::
                 (d.FStarC_Custard_Syntax.dl_flags))
             })
    | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DType d) ->
        FStarC_SMap.add st.emitted key
          (FStarC_Custard_Syntax.DType
             {
               FStarC_Custard_Syntax.dt_name =
                 (d.FStarC_Custard_Syntax.dt_name);
               FStarC_Custard_Syntax.dt_params =
                 (d.FStarC_Custard_Syntax.dt_params);
               FStarC_Custard_Syntax.dt_body =
                 (d.FStarC_Custard_Syntax.dt_body);
               FStarC_Custard_Syntax.dt_flags = (f ::
                 (d.FStarC_Custard_Syntax.dt_flags))
             })
    | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.DExternal d) ->
        FStarC_SMap.add st.emitted key
          (FStarC_Custard_Syntax.DExternal
             {
               FStarC_Custard_Syntax.dx_name =
                 (d.FStarC_Custard_Syntax.dx_name);
               FStarC_Custard_Syntax.dx_typars =
                 (d.FStarC_Custard_Syntax.dx_typars);
               FStarC_Custard_Syntax.dx_ty = (d.FStarC_Custard_Syntax.dx_ty);
               FStarC_Custard_Syntax.dx_target =
                 (d.FStarC_Custard_Syntax.dx_target);
               FStarC_Custard_Syntax.dx_header =
                 (d.FStarC_Custard_Syntax.dx_header);
               FStarC_Custard_Syntax.dx_flags = (f ::
                 (d.FStarC_Custard_Syntax.dx_flags))
             })
    | FStar_Pervasives_Native.Some uu___2 -> ()
    | FStar_Pervasives_Native.None when quiet -> ()
    | FStar_Pervasives_Native.None ->
        FStarC_Errors.log_issue0
          FStarC_Errors_Codes.Error_CustardEntryNotFound ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                (Prims.strcat "Custard entry point "
                   (Prims.strcat (FStarC_Ident.string_of_lid l)
                      " did not produce a declaration."));
             FStarC_Errors_Msg.text
               "It may be misspelled, or erased, or not defined in the module named."]) in
  let mark = mark' false in
  FStarC_List.iter
    (fun l -> FStarC_SMap.add st.roots (FStarC_Ident.string_of_lid l) true)
    roots;
  (let uu___2 = FStarC_Custard_Builtins.registered_roots () in
   FStarC_List.iter
     (fun l -> FStarC_SMap.add st.roots (FStarC_Ident.string_of_lid l) true)
     uu___2);
  (let uu___2 =
     FStarC_List.partition
       (fun l ->
          let uu___3 =
            FStarC_Custard_Loader.candidate_files st.deps
              (FStarC_Ident.string_of_lid l) in
          match uu___3 with | hd::tl -> true | uu___4 -> false) roots in
   match uu___2 with
   | (modroots, roots1) ->
       (FStarC_Custard_Prof.timed "run.modroots"
          (fun uu___4 ->
             FStarC_List.iter
               (fun l ->
                  let uu___5 =
                    let uu___6 = tcenv st in
                    FStarC_Custard_Loader.ensure_loaded st.deps uu___6
                      (FStarC_Ident.string_of_lid l) in
                  FStarC_Effect.op_Colon_Equals st.env uu___5) modroots);
        FStarC_Custard_Prof.timed "run.entry_modules"
          (fun uu___5 ->
             let uu___6 = FStarC_Options.custard_entry_modules () in
             FStarC_List.iter
               (fun m ->
                  (let uu___8 =
                     let uu___9 = tcenv st in
                     FStarC_Custard_Loader.ensure_loaded st.deps uu___9 m in
                   FStarC_Effect.op_Colon_Equals st.env uu___8);
                  (let uu___8 =
                     let uu___9 =
                       let uu___10 = tcenv st in
                       FStarC_TypeChecker_Env.modules uu___10 in
                     FStarC_List.tryFind
                       (fun md ->
                          (FStarC_Ident.string_of_lid
                             md.FStarC_Syntax_Syntax.name)
                            = m) uu___9 in
                   match uu___8 with
                   | FStar_Pervasives_Native.None ->
                       FStarC_Errors.log_issue0
                         FStarC_Errors_Codes.Error_CustardEntryNotFound ()
                         (Obj.magic
                            FStarC_Errors_Msg.is_error_message_list_doc)
                         (Obj.magic
                            [FStarC_Errors_Msg.text
                               (Prims.strcat "Custard entry module "
                                  (Prims.strcat m " was not loaded."));
                            FStarC_Errors_Msg.text
                              "It may be misspelled, or not among the input files."])
                   | FStar_Pervasives_Native.Some md ->
                       FStarC_List.iter
                         (fun se ->
                            match se.FStarC_Syntax_Syntax.sigel with
                            | FStarC_Syntax_Syntax.Sig_let
                                { FStarC_Syntax_Syntax.lbs1 = (uu___9, lbs);
                                  FStarC_Syntax_Syntax.lids1 = uu___10;_}
                                when
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_List.existsb
                                      (fun uu___13 ->
                                         match uu___13 with
                                         | FStarC_Syntax_Syntax.NoExtract ->
                                             true
                                         | FStarC_Syntax_Syntax.Projector
                                             uu___14 -> true
                                         | FStarC_Syntax_Syntax.Discriminator
                                             uu___14 -> true
                                         | uu___14 -> false)
                                      se.FStarC_Syntax_Syntax.sigquals in
                                  Prims.not uu___12 in
                                if uu___11
                                then
                                  let uu___12 = noextract_to_this_backend se in
                                  Prims.not uu___12
                                else false ->
                                FStarC_List.iter
                                  (fun lb ->
                                     match lb.FStarC_Syntax_Syntax.lbname
                                     with
                                     | FStar_Pervasives.Inr fv when
                                         let uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               erased_definition st
                                                 lb.FStarC_Syntax_Syntax.lbtyp in
                                             Prims.not uu___13 in
                                           if uu___12
                                           then true
                                           else
                                             is_type_sig st
                                               lb.FStarC_Syntax_Syntax.lbtyp in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             unrootable_definition st
                                               lb.FStarC_Syntax_Syntax.lbtyp in
                                           Prims.not uu___12
                                         else false ->
                                         mark' true
                                           FStarC_Custard_Syntax.Root
                                           (FStarC_Syntax_Syntax.lid_of_fv fv)
                                     | uu___11 -> ()) lbs
                            | uu___9 -> ())
                         md.FStarC_Syntax_Syntax.declarations)) uu___6);
        FStarC_Custard_Prof.timed "run.roots"
          (fun uu___6 ->
             FStarC_List.iter
               (fun l ->
                  let uu___8 =
                    let uu___9 = root_is_erased st l in Prims.not uu___9 in
                  if uu___8 then mark FStarC_Custard_Syntax.Root l else ())
               roots1;
             (let uu___8 = FStarC_Custard_Builtins.registered_roots () in
              FStarC_List.iter
                (fun l ->
                   let uu___9 =
                     let uu___10 = root_is_erased st l in Prims.not uu___10 in
                   if uu___9 then mark FStarC_Custard_Syntax.Root l else ())
                uu___8));
        FStarC_Custard_Prof.timed "run.main"
          (fun uu___7 ->
             match main with
             | FStar_Pervasives_Native.Some l ->
                 mark FStarC_Custard_Syntax.Entrypoint l
             | FStar_Pervasives_Native.None -> ());
        (let seen_inits = FStarC_SMap.create (Prims.of_int 100) in
         let rec inits fuel =
           if fuel <= Prims.int_zero
           then ()
           else
             (let fresh =
                let uu___7 =
                  let uu___8 = tcenv st in
                  FStarC_TypeChecker_Env.modules uu___8 in
                FStarC_List.collect
                  (fun md ->
                     let m =
                       FStarC_Ident.string_of_lid
                         md.FStarC_Syntax_Syntax.name in
                     let uu___8 = FStarC_SMap.try_find seen_inits m in
                     match uu___8 with
                     | FStar_Pervasives_Native.Some () -> []
                     | FStar_Pervasives_Native.None ->
                         (FStarC_SMap.add seen_inits m (); [md])) uu___7 in
              if match fresh with | [] -> true | uu___7 -> false
              then ()
              else
                (FStarC_Custard_Prof.timed "inits"
                   (fun uu___8 ->
                      FStarC_List.iter
                        (fun md ->
                           FStarC_List.iter
                             (fun se ->
                                match se.FStarC_Syntax_Syntax.sigel with
                                | FStarC_Syntax_Syntax.Sig_let
                                    {
                                      FStarC_Syntax_Syntax.lbs1 =
                                        (uu___9, lbs);
                                      FStarC_Syntax_Syntax.lids1 = uu___10;_}
                                    ->
                                    FStarC_List.iter
                                      (fun lb ->
                                         match lb.FStarC_Syntax_Syntax.lbname
                                         with
                                         | FStar_Pervasives.Inr fv when
                                             Prims.not
                                               (FStarC_Syntax_Util.is_pure_or_ghost_effect
                                                  lb.FStarC_Syntax_Syntax.lbeff)
                                             ->
                                             mark' true
                                               FStarC_Custard_Syntax.Root
                                               (FStarC_Syntax_Syntax.lid_of_fv
                                                  fv)
                                         | uu___11 -> ()) lbs
                                | uu___9 -> ())
                             md.FStarC_Syntax_Syntax.declarations) fresh);
                 FStarC_Custard_Prof.timed "regemb"
                   (fun uu___9 -> FStarC_List.iter per_module fresh);
                 inits (fuel - Prims.int_one))) in
         FStarC_Custard_Prof.timed "run.inits"
           (fun uu___8 -> inits (Prims.of_int 100));
         (let uu___9 = FStarC_Options.custard_dump_specializations () in
          if uu___9 then dump_specializations st else ());
         FStarC_Custard_Prof.timed "run.collect"
           (fun uu___9 ->
              let uu___10 = FStarC_Custard_Builtins.take_lifted () in
              let uu___11 =
                let uu___12 =
                  let uu___13 = FStarC_Effect.op_Bang st.order in
                  FStarC_List.rev uu___13 in
                FStarC_List.collect
                  (fun key ->
                     let uu___13 = FStarC_SMap.try_find st.emitted key in
                     match uu___13 with
                     | FStar_Pervasives_Native.Some d -> [d]
                     | FStar_Pervasives_Native.None -> []) uu___12 in
              FStarC_List.op_At uu___10 uu___11))))
let request_lid (st : state) (l : FStarC_Ident.lident) :
  FStarC_Custard_Syntax.name=
  request st
    { sk_lid = l; sk_args = []; sk_subst = []; sk_holes = Prims.int_zero }
let emit (st : state) (key : Prims.string) (d : FStarC_Custard_Syntax.decl) :
  unit=
  let uu___ = FStarC_SMap.try_find st.emitted key in
  match uu___ with
  | FStar_Pervasives_Native.Some uu___1 -> ()
  | FStar_Pervasives_Native.None ->
      (FStarC_SMap.add st.emitted key d;
       (let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang st.order in key :: uu___3 in
        FStarC_Effect.op_Colon_Equals st.order uu___2))
let emitted (st : state) (key : Prims.string) : Prims.bool=
  let uu___ = FStarC_SMap.try_find st.emitted key in
  match uu___ with | FStar_Pervasives_Native.Some v -> true | uu___1 -> false
let imports (st : state) :
  (FStarC_Custard_Syntax.decl * FStarC_Custard_Syntax.type_info
    FStar_Pervasives_Native.option) Prims.list=
  let uu___ = FStarC_Effect.op_Bang st.imports in FStarC_List.rev uu___
let link_homes (st : state) : Prims.string Prims.list=
  FStarC_Custard_Unit.link_homes st.links
let link_headers (st : state) : Prims.string Prims.list=
  FStarC_Custard_Unit.link_headers st.links
let link_no_prefix (st : state) : Prims.string Prims.list=
  FStarC_Custard_Unit.link_no_prefix st.links
let link_inits (st : state) : Prims.string Prims.list=
  FStarC_Custard_Unit.link_inits st.links
let exported_keys (st : state) : (Prims.string * Prims.string) Prims.list=
  FStarC_SMap.fold st.names
    (fun key nm acc ->
       let uu___ =
         let uu___1 = FStarC_Custard_Syntax.string_of_name nm in
         (uu___1, key) in
       uu___ :: acc) []
let loaded_digests (uu___ : state) :
  (Prims.string * Prims.string) Prims.list=
  FStarC_Custard_Loader.loaded_digests ()
let adopt_type_clones (st : state) (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.program=
  FStarC_List.collect
    (fun d ->
       match d with
       | FStarC_Custard_Syntax.DType dt when
           let uu___ = FStarC_Custard_Syntax.imported_unit d in
           match uu___ with
           | FStar_Pervasives_Native.None -> true
           | uu___1 -> false ->
           let uu___ =
             let uu___1 =
               FStarC_Custard_Unit.type_key dt.FStarC_Custard_Syntax.dt_name in
             FStarC_Custard_Unit.lookup st.links uu___1 in
           (match uu___ with
            | FStar_Pervasives_Native.Some (u, e) ->
                (match e.FStarC_Custard_Unit.ue_decl with
                 | FStarC_Custard_Syntax.DType dt' ->
                     let d' =
                       FStarC_Custard_Syntax.DType
                         {
                           FStarC_Custard_Syntax.dt_name =
                             (dt'.FStarC_Custard_Syntax.dt_name);
                           FStarC_Custard_Syntax.dt_params =
                             (dt'.FStarC_Custard_Syntax.dt_params);
                           FStarC_Custard_Syntax.dt_body =
                             (dt'.FStarC_Custard_Syntax.dt_body);
                           FStarC_Custard_Syntax.dt_flags =
                             ((FStarC_Custard_Syntax.Imported
                                 (u, (e.FStarC_Custard_Unit.ue_home))) ::
                             (dt'.FStarC_Custard_Syntax.dt_flags))
                         } in
                     ((let uu___2 =
                         let uu___3 = FStarC_Effect.op_Bang st.imports in
                         (d', (e.FStarC_Custard_Unit.ue_type)) :: uu___3 in
                       FStarC_Effect.op_Colon_Equals st.imports uu___2);
                      (let uu___3 =
                         FStarC_Options.custard_dump_specializations () in
                       if uu___3
                       then
                         let uu___4 =
                           FStarC_Custard_Syntax.string_of_name
                             dt.FStarC_Custard_Syntax.dt_name in
                         FStarC_Format.print2
                           "Custard: the type %s comes from unit %s\n" uu___4
                           u
                       else ());
                      [])
                 | uu___1 -> [d])
            | FStar_Pervasives_Native.None -> [d])
       | uu___ -> [d]) prog
