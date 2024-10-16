open Prims
type 't mm = Prims.bool -> ('t * Prims.bool)
let op_let_Question : 's 't . 't mm -> ('t -> 's mm) -> 's mm =
  fun f ->
    fun g ->
      fun b ->
        let uu___ = f b in
        match uu___ with | (t1, b1) -> let uu___1 = g t1 in uu___1 b1
let ret : 't . 't -> 't mm = fun x -> fun b -> (x, b)
let (should_memo : Prims.bool mm) = fun b -> (b, b)
let (no_memo : unit mm) = fun uu___ -> ((), false)
let maybe_memoize :
  'a .
    'a FStarC_Syntax_Syntax.syntax ->
      ('a FStarC_Syntax_Syntax.syntax -> FStarC_Hash.hash_code mm) ->
        FStarC_Hash.hash_code mm
  =
  fun h ->
    fun f ->
      fun should_memo1 ->
        if should_memo1
        then
          let uu___ =
            FStarC_Compiler_Effect.op_Bang h.FStarC_Syntax_Syntax.hash_code in
          match uu___ with
          | FStar_Pervasives_Native.Some c -> (c, should_memo1)
          | FStar_Pervasives_Native.None ->
              let uu___1 = let uu___2 = f h in uu___2 should_memo1 in
              (match uu___1 with
               | (c, should_memo2) ->
                   (if should_memo2
                    then
                      FStarC_Compiler_Effect.op_Colon_Equals
                        h.FStarC_Syntax_Syntax.hash_code
                        (FStar_Pervasives_Native.Some c)
                    else ();
                    (c, should_memo2)))
        else (let uu___1 = f h in uu___1 should_memo1)
let (of_int : Prims.int -> FStarC_Hash.hash_code mm) =
  fun i -> let uu___ = FStarC_Hash.of_int i in ret uu___
let (of_string : Prims.string -> FStarC_Hash.hash_code mm) =
  fun s -> let uu___ = FStarC_Hash.of_string s in ret uu___
let (mix :
  FStarC_Hash.hash_code mm ->
    FStarC_Hash.hash_code mm -> FStarC_Hash.hash_code mm)
  =
  fun f ->
    fun g ->
      fun b ->
        let uu___ = f b in
        match uu___ with
        | (x, b0) ->
            let uu___1 = g b in
            (match uu___1 with
             | (y, b1) ->
                 let uu___2 = FStarC_Hash.mix x y in (uu___2, (b0 && b1)))
let (nil_hc : FStarC_Hash.hash_code mm) = of_int (Prims.of_int (1229))
let (cons_hc : FStarC_Hash.hash_code mm) = of_int (Prims.of_int (1231))
let (mix_list :
  FStarC_Hash.hash_code mm Prims.list -> FStarC_Hash.hash_code mm) =
  fun l -> FStarC_Compiler_List.fold_right mix l nil_hc
let (mix_list_lit :
  FStarC_Hash.hash_code mm Prims.list -> FStarC_Hash.hash_code mm) = mix_list
let hash_list :
  'a .
    ('a -> FStarC_Hash.hash_code mm) ->
      'a Prims.list -> FStarC_Hash.hash_code mm
  =
  fun h ->
    fun ts -> let uu___ = FStarC_Compiler_List.map h ts in mix_list uu___
let hash_option :
  'a .
    ('a -> FStarC_Hash.hash_code mm) ->
      'a FStar_Pervasives_Native.option -> FStarC_Hash.hash_code mm
  =
  fun h ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.None ->
          let uu___ = FStarC_Hash.of_int (Prims.of_int (1237)) in ret uu___
      | FStar_Pervasives_Native.Some o1 ->
          let uu___ =
            let uu___1 = FStarC_Hash.of_int (Prims.of_int (1249)) in
            ret uu___1 in
          let uu___1 = h o1 in mix uu___ uu___1
let (hash_doc : FStarC_Pprint.document -> FStarC_Hash.hash_code mm) =
  fun d ->
    let uu___ =
      FStarC_Pprint.pretty_string
        (FStarC_Compiler_Util.float_of_string "1.0") (Prims.of_int (80)) d in
    of_string uu___
let (hash_doc_list :
  FStarC_Pprint.document Prims.list -> FStarC_Hash.hash_code mm) =
  fun ds -> hash_list hash_doc ds
let hash_pair :
  'a 'b .
    ('a -> FStarC_Hash.hash_code mm) ->
      ('b -> FStarC_Hash.hash_code mm) ->
        ('a * 'b) -> FStarC_Hash.hash_code mm
  =
  fun h ->
    fun i ->
      fun x ->
        let uu___ = h (FStar_Pervasives_Native.fst x) in
        let uu___1 = i (FStar_Pervasives_Native.snd x) in mix uu___ uu___1
let rec (hash_term : FStarC_Syntax_Syntax.term -> FStarC_Hash.hash_code mm) =
  fun t -> maybe_memoize t hash_term'
and (hash_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Hash.hash_code mm)
  = fun c -> maybe_memoize c hash_comp'
and (hash_term' : FStarC_Syntax_Syntax.term -> FStarC_Hash.hash_code mm) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_bvar bv ->
        let uu___1 = of_int (Prims.of_int (3)) in
        let uu___2 = of_int bv.FStarC_Syntax_Syntax.index in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_name bv ->
        let uu___1 = of_int (Prims.of_int (5)) in
        let uu___2 = of_int bv.FStarC_Syntax_Syntax.index in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_fvar fv ->
        let uu___1 = of_int (Prims.of_int (7)) in
        let uu___2 = hash_fv fv in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu___1 = of_int (Prims.of_int (11)) in
        let uu___2 =
          let uu___3 = hash_term t1 in
          let uu___4 = hash_list hash_universe us in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_constant sc ->
        let uu___1 = of_int (Prims.of_int (13)) in
        let uu___2 = hash_constant sc in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_type u ->
        let uu___1 = of_int (Prims.of_int (17)) in
        let uu___2 = hash_universe u in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = t1;
          FStarC_Syntax_Syntax.rc_opt = rcopt;_}
        ->
        let uu___1 = of_int (Prims.of_int (19)) in
        let uu___2 =
          let uu___3 = hash_list hash_binder bs in
          let uu___4 =
            let uu___5 = hash_term t1 in
            let uu___6 = hash_option hash_rc rcopt in mix uu___5 uu___6 in
          mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_} ->
        let uu___1 = of_int (Prims.of_int (23)) in
        let uu___2 =
          let uu___3 = hash_list hash_binder bs in
          let uu___4 = hash_comp c in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = b; FStarC_Syntax_Syntax.phi = t1;_} ->
        let uu___1 = of_int (Prims.of_int (29)) in
        let uu___2 =
          let uu___3 = hash_bv b in
          let uu___4 = hash_term t1 in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t1; FStarC_Syntax_Syntax.args = args;_}
        ->
        let uu___1 = of_int (Prims.of_int (31)) in
        let uu___2 =
          let uu___3 = hash_term t1 in
          let uu___4 = hash_list hash_arg args in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = t1;
          FStarC_Syntax_Syntax.ret_opt = asc_opt;
          FStarC_Syntax_Syntax.brs = branches;
          FStarC_Syntax_Syntax.rc_opt1 = rcopt;_}
        ->
        let uu___1 = of_int (Prims.of_int (37)) in
        let uu___2 =
          let uu___3 = hash_option hash_match_returns asc_opt in
          let uu___4 =
            let uu___5 =
              let uu___6 = hash_term t1 in
              let uu___7 = hash_list hash_branch branches in
              mix uu___6 uu___7 in
            let uu___6 = hash_option hash_rc rcopt in mix uu___5 uu___6 in
          mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = a;
          FStarC_Syntax_Syntax.eff_opt = lopt;_}
        ->
        let uu___1 = of_int (Prims.of_int (43)) in
        let uu___2 =
          let uu___3 = hash_term t1 in
          let uu___4 =
            let uu___5 = hash_ascription a in
            let uu___6 = hash_option hash_lid lopt in mix uu___5 uu___6 in
          mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
          FStarC_Syntax_Syntax.body1 = t1;_}
        ->
        let uu___1 = of_int (Prims.of_int (47)) in
        let uu___2 =
          let uu___3 = hash_lb lb in
          let uu___4 = hash_term t1 in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (uu___1, lbs);
          FStarC_Syntax_Syntax.body1 = t1;_}
        ->
        let uu___2 = of_int (Prims.of_int (51)) in
        let uu___3 =
          let uu___4 = hash_list hash_lb lbs in
          let uu___5 = hash_term t1 in mix uu___4 uu___5 in
        mix uu___2 uu___3
    | FStarC_Syntax_Syntax.Tm_uvar uv ->
        let uu___1 = of_int (Prims.of_int (53)) in
        let uu___2 = hash_uvar uv in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = m;_} ->
        let uu___1 = of_int (Prims.of_int (61)) in
        let uu___2 =
          let uu___3 = hash_term t1 in
          let uu___4 = hash_meta m in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_lazy li ->
        let uu___1 = of_int (Prims.of_int (67)) in
        let uu___2 = hash_lazyinfo li in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_quoted (t1, qi) ->
        let uu___1 = of_int (Prims.of_int (71)) in
        let uu___2 =
          let uu___3 = hash_term t1 in
          let uu___4 = hash_quoteinfo qi in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Tm_unknown -> of_int (Prims.of_int (73))
    | FStarC_Syntax_Syntax.Tm_delayed uu___1 -> failwith "Impossible"
and (hash_comp' : FStarC_Syntax_Syntax.comp -> FStarC_Hash.hash_code mm) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (811)) in
          let uu___2 = let uu___3 = hash_term t in [uu___3] in uu___1 ::
            uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.GTotal t ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (821)) in
          let uu___2 = let uu___3 = hash_term t in [uu___3] in uu___1 ::
            uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Comp ct ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (823)) in
          let uu___2 =
            let uu___3 =
              hash_list hash_universe ct.FStarC_Syntax_Syntax.comp_univs in
            let uu___4 =
              let uu___5 = hash_lid ct.FStarC_Syntax_Syntax.effect_name in
              let uu___6 =
                let uu___7 = hash_term ct.FStarC_Syntax_Syntax.result_typ in
                let uu___8 =
                  let uu___9 =
                    hash_list hash_arg ct.FStarC_Syntax_Syntax.effect_args in
                  let uu___10 =
                    let uu___11 =
                      hash_list hash_flag ct.FStarC_Syntax_Syntax.flags in
                    [uu___11] in
                  uu___9 :: uu___10 in
                uu___7 :: uu___8 in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mix_list_lit uu___
and (hash_lb : FStarC_Syntax_Syntax.letbinding -> FStarC_Hash.hash_code mm) =
  fun lb ->
    let uu___ =
      let uu___1 = of_int (Prims.of_int (79)) in
      let uu___2 =
        let uu___3 = hash_lbname lb.FStarC_Syntax_Syntax.lbname in
        let uu___4 =
          let uu___5 = hash_list hash_ident lb.FStarC_Syntax_Syntax.lbunivs in
          let uu___6 =
            let uu___7 = hash_term lb.FStarC_Syntax_Syntax.lbtyp in
            let uu___8 =
              let uu___9 = hash_lid lb.FStarC_Syntax_Syntax.lbeff in
              let uu___10 =
                let uu___11 = hash_term lb.FStarC_Syntax_Syntax.lbdef in
                let uu___12 =
                  let uu___13 =
                    hash_list hash_term lb.FStarC_Syntax_Syntax.lbattrs in
                  [uu___13] in
                uu___11 :: uu___12 in
              uu___9 :: uu___10 in
            uu___7 :: uu___8 in
          uu___5 :: uu___6 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mix_list_lit uu___
and (hash_match_returns :
  (FStarC_Syntax_Syntax.binder *
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option * Prims.bool))
    -> FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | (b, asc) ->
        let uu___1 = hash_binder b in
        let uu___2 = hash_ascription asc in mix uu___1 uu___2
and (hash_branch :
  (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax) -> FStarC_Hash.hash_code mm)
  =
  fun b ->
    let uu___ = b in
    match uu___ with
    | (p, topt, t) ->
        let uu___1 =
          let uu___2 = of_int (Prims.of_int (83)) in
          let uu___3 =
            let uu___4 = hash_pat p in
            let uu___5 =
              let uu___6 = hash_option hash_term topt in
              let uu___7 = let uu___8 = hash_term t in [uu___8] in uu___6 ::
                uu___7 in
            uu___4 :: uu___5 in
          uu___2 :: uu___3 in
        mix_list_lit uu___1
and (hash_pat :
  FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t ->
    FStarC_Hash.hash_code mm)
  =
  fun p ->
    match p.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_constant c ->
        let uu___ = of_int (Prims.of_int (89)) in
        let uu___1 = hash_constant c in mix uu___ uu___1
    | FStarC_Syntax_Syntax.Pat_cons (fv, us, args) ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (97)) in
          let uu___2 =
            let uu___3 = hash_fv fv in
            let uu___4 =
              let uu___5 = hash_option (hash_list hash_universe) us in
              let uu___6 =
                let uu___7 = hash_list (hash_pair hash_pat hash_bool) args in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Pat_var bv ->
        let uu___ = of_int (Prims.of_int (101)) in
        let uu___1 = hash_bv bv in mix uu___ uu___1
    | FStarC_Syntax_Syntax.Pat_dot_term t ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (107)) in
          let uu___2 = let uu___3 = hash_option hash_term t in [uu___3] in
          uu___1 :: uu___2 in
        mix_list_lit uu___
and (hash_bv : FStarC_Syntax_Syntax.bv -> FStarC_Hash.hash_code mm) =
  fun b -> hash_term b.FStarC_Syntax_Syntax.sort
and (hash_fv : FStarC_Syntax_Syntax.fv -> FStarC_Hash.hash_code mm) =
  fun fv ->
    let uu___ =
      FStarC_Ident.string_of_lid
        (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
    of_string uu___
and (hash_binder : FStarC_Syntax_Syntax.binder -> FStarC_Hash.hash_code mm) =
  fun b ->
    let uu___ =
      let uu___1 = hash_bv b.FStarC_Syntax_Syntax.binder_bv in
      let uu___2 =
        let uu___3 =
          hash_option hash_bqual b.FStarC_Syntax_Syntax.binder_qual in
        let uu___4 =
          let uu___5 =
            hash_list hash_term b.FStarC_Syntax_Syntax.binder_attrs in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mix_list_lit uu___
and (hash_universe :
  FStarC_Syntax_Syntax.universe -> FStarC_Hash.hash_code mm) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.U_zero -> of_int (Prims.of_int (179))
    | FStarC_Syntax_Syntax.U_succ u ->
        let uu___1 = of_int (Prims.of_int (181)) in
        let uu___2 = hash_universe u in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.U_max us ->
        let uu___1 = of_int (Prims.of_int (191)) in
        let uu___2 = hash_list hash_universe us in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.U_bvar i ->
        let uu___1 = of_int (Prims.of_int (193)) in
        let uu___2 = of_int i in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.U_name i ->
        let uu___1 = of_int (Prims.of_int (197)) in
        let uu___2 = hash_ident i in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.U_unif uv ->
        let uu___1 = of_int (Prims.of_int (199)) in
        let uu___2 = hash_universe_uvar uv in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.U_unknown -> of_int (Prims.of_int (211))
and (hash_arg :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
    FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | (t, aq) ->
        let uu___1 = hash_term t in
        let uu___2 = hash_option hash_arg_qualifier aq in mix uu___1 uu___2
and (hash_arg_qualifier :
  FStarC_Syntax_Syntax.arg_qualifier -> FStarC_Hash.hash_code mm) =
  fun aq ->
    let uu___ = hash_bool aq.FStarC_Syntax_Syntax.aqual_implicit in
    let uu___1 = hash_list hash_term aq.FStarC_Syntax_Syntax.aqual_attributes in
    mix uu___ uu___1
and (hash_bqual :
  FStarC_Syntax_Syntax.binder_qualifier -> FStarC_Hash.hash_code mm) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Implicit (true) -> of_int (Prims.of_int (419))
    | FStarC_Syntax_Syntax.Implicit (false) -> of_int (Prims.of_int (421))
    | FStarC_Syntax_Syntax.Meta t ->
        let uu___1 = of_int (Prims.of_int (431)) in
        let uu___2 = hash_term t in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.Equality -> of_int (Prims.of_int (433))
and (hash_uvar :
  (FStarC_Syntax_Syntax.ctx_uvar * (FStarC_Syntax_Syntax.subst_elt Prims.list
    Prims.list * FStarC_Syntax_Syntax.maybe_set_use_range)) ->
    FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | (u, uu___1) ->
        let uu___2 =
          FStarC_Syntax_Unionfind.uvar_id
            u.FStarC_Syntax_Syntax.ctx_uvar_head in
        of_int uu___2
and (hash_universe_uvar :
  (FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStarC_Unionfind.p_uvar * FStarC_Syntax_Syntax.version *
    FStarC_Compiler_Range_Type.range) -> FStarC_Hash.hash_code mm)
  =
  fun u -> let uu___ = FStarC_Syntax_Unionfind.univ_uvar_id u in of_int uu___
and (hash_ascription :
  ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option * Prims.bool)
    -> FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | (a, to1, b) ->
        let uu___1 =
          match a with
          | FStar_Pervasives.Inl t -> hash_term t
          | FStar_Pervasives.Inr c -> hash_comp c in
        let uu___2 = hash_option hash_term to1 in mix uu___1 uu___2
and (hash_bool : Prims.bool -> FStarC_Hash.hash_code mm) =
  fun b ->
    if b then of_int (Prims.of_int (307)) else of_int (Prims.of_int (311))
and (hash_constant : FStarC_Syntax_Syntax.sconst -> FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | FStarC_Const.Const_effect -> of_int (Prims.of_int (283))
    | FStarC_Const.Const_unit -> of_int (Prims.of_int (293))
    | FStarC_Const.Const_bool b -> hash_bool b
    | FStarC_Const.Const_int (s, o) ->
        let uu___1 = of_int (Prims.of_int (313)) in
        let uu___2 =
          let uu___3 = of_string s in
          let uu___4 = hash_option hash_sw o in mix uu___3 uu___4 in
        mix uu___1 uu___2
    | FStarC_Const.Const_char c ->
        let uu___1 = of_int (Prims.of_int (317)) in
        let uu___2 = of_int (FStar_Char.int_of_char c) in mix uu___1 uu___2
    | FStarC_Const.Const_real s ->
        let uu___1 = of_int (Prims.of_int (337)) in
        let uu___2 = of_string s in mix uu___1 uu___2
    | FStarC_Const.Const_string (s, uu___1) ->
        let uu___2 = of_int (Prims.of_int (349)) in
        let uu___3 = of_string s in mix uu___2 uu___3
    | FStarC_Const.Const_range_of -> of_int (Prims.of_int (353))
    | FStarC_Const.Const_set_range_of -> of_int (Prims.of_int (359))
    | FStarC_Const.Const_range r ->
        let uu___1 = of_int (Prims.of_int (367)) in
        let uu___2 =
          let uu___3 = FStarC_Compiler_Range_Ops.string_of_range r in
          of_string uu___3 in
        mix uu___1 uu___2
    | FStarC_Const.Const_reify uu___1 -> of_int (Prims.of_int (367))
    | FStarC_Const.Const_reflect l ->
        let uu___1 = of_int (Prims.of_int (373)) in
        let uu___2 = hash_lid l in mix uu___1 uu___2
and (hash_sw :
  (FStarC_Const.signedness * FStarC_Const.width) -> FStarC_Hash.hash_code mm)
  =
  fun uu___ ->
    match uu___ with
    | (s, w) ->
        let uu___1 =
          match s with
          | FStarC_Const.Unsigned -> of_int (Prims.of_int (547))
          | FStarC_Const.Signed -> of_int (Prims.of_int (557)) in
        let uu___2 =
          match w with
          | FStarC_Const.Int8 -> of_int (Prims.of_int (563))
          | FStarC_Const.Int16 -> of_int (Prims.of_int (569))
          | FStarC_Const.Int32 -> of_int (Prims.of_int (571))
          | FStarC_Const.Int64 -> of_int (Prims.of_int (577))
          | FStarC_Const.Sizet -> of_int (Prims.of_int (583)) in
        mix uu___1 uu___2
and (hash_ident : FStarC_Syntax_Syntax.univ_name -> FStarC_Hash.hash_code mm)
  = fun i -> let uu___ = FStarC_Ident.string_of_id i in of_string uu___
and (hash_lid : FStarC_Ident.lident -> FStarC_Hash.hash_code mm) =
  fun l -> let uu___ = FStarC_Ident.string_of_lid l in of_string uu___
and (hash_lbname :
  (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv) FStar_Pervasives.either
    -> FStarC_Hash.hash_code mm)
  =
  fun l ->
    match l with
    | FStar_Pervasives.Inl bv -> hash_bv bv
    | FStar_Pervasives.Inr fv -> hash_fv fv
and (hash_rc :
  FStarC_Syntax_Syntax.residual_comp -> FStarC_Hash.hash_code mm) =
  fun rc ->
    let uu___ =
      let uu___1 = hash_lid rc.FStarC_Syntax_Syntax.residual_effect in
      let uu___2 =
        let uu___3 =
          hash_option hash_term rc.FStarC_Syntax_Syntax.residual_typ in
        let uu___4 =
          let uu___5 =
            hash_list hash_flag rc.FStarC_Syntax_Syntax.residual_flags in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    mix_list_lit uu___
and (hash_flag : FStarC_Syntax_Syntax.cflag -> FStarC_Hash.hash_code mm) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.TOTAL -> of_int (Prims.of_int (947))
    | FStarC_Syntax_Syntax.MLEFFECT -> of_int (Prims.of_int (953))
    | FStarC_Syntax_Syntax.LEMMA -> of_int (Prims.of_int (967))
    | FStarC_Syntax_Syntax.RETURN -> of_int (Prims.of_int (971))
    | FStarC_Syntax_Syntax.PARTIAL_RETURN -> of_int (Prims.of_int (977))
    | FStarC_Syntax_Syntax.SOMETRIVIAL -> of_int (Prims.of_int (983))
    | FStarC_Syntax_Syntax.TRIVIAL_POSTCONDITION ->
        of_int (Prims.of_int (991))
    | FStarC_Syntax_Syntax.SHOULD_NOT_INLINE -> of_int (Prims.of_int (997))
    | FStarC_Syntax_Syntax.CPS -> of_int (Prims.of_int (1009))
    | FStarC_Syntax_Syntax.DECREASES (FStarC_Syntax_Syntax.Decreases_lex ts)
        ->
        let uu___1 = of_int (Prims.of_int (1013)) in
        let uu___2 = hash_list hash_term ts in mix uu___1 uu___2
    | FStarC_Syntax_Syntax.DECREASES (FStarC_Syntax_Syntax.Decreases_wf
        (t0, t1)) ->
        let uu___1 = of_int (Prims.of_int (2341)) in
        let uu___2 = hash_list hash_term [t0; t1] in mix uu___1 uu___2
and (hash_meta : FStarC_Syntax_Syntax.metadata -> FStarC_Hash.hash_code mm) =
  fun m ->
    match m with
    | FStarC_Syntax_Syntax.Meta_pattern (ts, args) ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (1019)) in
          let uu___2 =
            let uu___3 = hash_list hash_term ts in
            let uu___4 =
              let uu___5 = hash_list (hash_list hash_arg) args in [uu___5] in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Meta_named l ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (1021)) in
          let uu___2 = let uu___3 = hash_lid l in [uu___3] in uu___1 ::
            uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Meta_labeled (s, r, uu___) ->
        let uu___1 =
          let uu___2 = of_int (Prims.of_int (1031)) in
          let uu___3 =
            let uu___4 = hash_doc_list s in
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Compiler_Range_Ops.string_of_range r in
                of_string uu___7 in
              [uu___6] in
            uu___4 :: uu___5 in
          uu___2 :: uu___3 in
        mix_list_lit uu___1
    | FStarC_Syntax_Syntax.Meta_desugared msi ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (1033)) in
          let uu___2 = let uu___3 = hash_meta_source_info msi in [uu___3] in
          uu___1 :: uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Meta_monadic (m1, t) ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (1039)) in
          let uu___2 =
            let uu___3 = hash_lid m1 in
            let uu___4 = let uu___5 = hash_term t in [uu___5] in uu___3 ::
              uu___4 in
          uu___1 :: uu___2 in
        mix_list_lit uu___
    | FStarC_Syntax_Syntax.Meta_monadic_lift (m0, m1, t) ->
        let uu___ =
          let uu___1 = of_int (Prims.of_int (1069)) in
          let uu___2 =
            let uu___3 = hash_lid m0 in
            let uu___4 =
              let uu___5 = hash_lid m1 in
              let uu___6 = let uu___7 = hash_term t in [uu___7] in uu___5 ::
                uu___6 in
            uu___3 :: uu___4 in
          uu___1 :: uu___2 in
        mix_list_lit uu___
and (hash_meta_source_info :
  FStarC_Syntax_Syntax.meta_source_info -> FStarC_Hash.hash_code mm) =
  fun m ->
    match m with
    | FStarC_Syntax_Syntax.Sequence -> of_int (Prims.of_int (1049))
    | FStarC_Syntax_Syntax.Primop -> of_int (Prims.of_int (1051))
    | FStarC_Syntax_Syntax.Masked_effect -> of_int (Prims.of_int (1061))
    | FStarC_Syntax_Syntax.Meta_smt_pat -> of_int (Prims.of_int (1063))
    | FStarC_Syntax_Syntax.Machine_integer sw ->
        let uu___ = of_int (Prims.of_int (1069)) in
        let uu___1 = hash_sw sw in mix uu___ uu___1
and (hash_lazyinfo :
  FStarC_Syntax_Syntax.lazyinfo -> FStarC_Hash.hash_code mm) =
  fun li -> of_int Prims.int_zero
and (hash_quoteinfo :
  FStarC_Syntax_Syntax.quoteinfo -> FStarC_Hash.hash_code mm) =
  fun qi ->
    let uu___ =
      hash_bool
        (qi.FStarC_Syntax_Syntax.qkind = FStarC_Syntax_Syntax.Quote_static) in
    let uu___1 =
      hash_list hash_term
        (FStar_Pervasives_Native.snd qi.FStarC_Syntax_Syntax.antiquotations) in
    mix uu___ uu___1
let rec equal_list :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1 -> Prims.bool) ->
      'uuuuu Prims.list -> 'uuuuu1 Prims.list -> Prims.bool
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> true
        | (h1::t1, h2::t2) -> (f h1 h2) && (equal_list f t1 t2)
        | uu___ -> false
let equal_opt :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1 -> Prims.bool) ->
      'uuuuu FStar_Pervasives_Native.option ->
        'uuuuu1 FStar_Pervasives_Native.option -> Prims.bool
  =
  fun f ->
    fun o1 ->
      fun o2 ->
        match (o1, o2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b) ->
            f a b
        | uu___ -> false
let equal_pair :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu -> 'uuuuu1 -> Prims.bool) ->
      ('uuuuu2 -> 'uuuuu3 -> Prims.bool) ->
        ('uuuuu * 'uuuuu2) -> ('uuuuu1 * 'uuuuu3) -> Prims.bool
  =
  fun f ->
    fun g ->
      fun uu___ ->
        fun uu___1 ->
          match (uu___, uu___1) with
          | ((x1, y1), (x2, y2)) -> (f x1 x2) && (g y1 y2)
let equal_poly : 'uuuuu . 'uuuuu -> 'uuuuu -> Prims.bool =
  fun x -> fun y -> x = y
let (ext_hash_term : FStarC_Syntax_Syntax.term -> FStarC_Hash.hash_code) =
  fun t ->
    let uu___ = let uu___1 = hash_term t in uu___1 true in
    FStar_Pervasives_Native.fst uu___
let (ext_hash_term_no_memo :
  FStarC_Syntax_Syntax.term -> FStarC_Hash.hash_code) =
  fun t ->
    let uu___ = let uu___1 = hash_term t in uu___1 false in
    FStar_Pervasives_Native.fst uu___
let rec (equal_term :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality t1 t2 in
      if uu___
      then true
      else
        (let uu___2 =
           FStarC_Compiler_Util.physical_equality t1.FStarC_Syntax_Syntax.n
             t2.FStarC_Syntax_Syntax.n in
         if uu___2
         then true
         else
           (let uu___4 =
              let uu___5 = ext_hash_term t1 in
              let uu___6 = ext_hash_term t2 in uu___5 <> uu___6 in
            if uu___4
            then false
            else
              (let uu___6 =
                 let uu___7 =
                   let uu___8 = FStarC_Syntax_Subst.compress t1 in
                   uu___8.FStarC_Syntax_Syntax.n in
                 let uu___8 =
                   let uu___9 = FStarC_Syntax_Subst.compress t2 in
                   uu___9.FStarC_Syntax_Syntax.n in
                 (uu___7, uu___8) in
               match uu___6 with
               | (FStarC_Syntax_Syntax.Tm_bvar x,
                  FStarC_Syntax_Syntax.Tm_bvar y) ->
                   x.FStarC_Syntax_Syntax.index =
                     y.FStarC_Syntax_Syntax.index
               | (FStarC_Syntax_Syntax.Tm_name x,
                  FStarC_Syntax_Syntax.Tm_name y) ->
                   x.FStarC_Syntax_Syntax.index =
                     y.FStarC_Syntax_Syntax.index
               | (FStarC_Syntax_Syntax.Tm_fvar f,
                  FStarC_Syntax_Syntax.Tm_fvar g) -> equal_fv f g
               | (FStarC_Syntax_Syntax.Tm_uinst (t11, u1),
                  FStarC_Syntax_Syntax.Tm_uinst (t21, u2)) ->
                   (equal_term t11 t21) && (equal_list equal_universe u1 u2)
               | (FStarC_Syntax_Syntax.Tm_constant c1,
                  FStarC_Syntax_Syntax.Tm_constant c2) ->
                   equal_constant c1 c2
               | (FStarC_Syntax_Syntax.Tm_type u1,
                  FStarC_Syntax_Syntax.Tm_type u2) -> equal_universe u1 u2
               | (FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = bs1;
                    FStarC_Syntax_Syntax.body = t11;
                    FStarC_Syntax_Syntax.rc_opt = rc1;_},
                  FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = bs2;
                    FStarC_Syntax_Syntax.body = t21;
                    FStarC_Syntax_Syntax.rc_opt = rc2;_})
                   ->
                   ((equal_list equal_binder bs1 bs2) && (equal_term t11 t21))
                     && (equal_opt equal_rc rc1 rc2)
               | (FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = bs1;
                    FStarC_Syntax_Syntax.comp = c1;_},
                  FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = bs2;
                    FStarC_Syntax_Syntax.comp = c2;_})
                   -> (equal_list equal_binder bs1 bs2) && (equal_comp c1 c2)
               | (FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = b1;
                    FStarC_Syntax_Syntax.phi = t11;_},
                  FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = b2;
                    FStarC_Syntax_Syntax.phi = t21;_})
                   -> (equal_bv b1 b2) && (equal_term t11 t21)
               | (FStarC_Syntax_Syntax.Tm_app
                  { FStarC_Syntax_Syntax.hd = t11;
                    FStarC_Syntax_Syntax.args = as1;_},
                  FStarC_Syntax_Syntax.Tm_app
                  { FStarC_Syntax_Syntax.hd = t21;
                    FStarC_Syntax_Syntax.args = as2;_})
                   -> (equal_term t11 t21) && (equal_list equal_arg as1 as2)
               | (FStarC_Syntax_Syntax.Tm_match
                  { FStarC_Syntax_Syntax.scrutinee = t11;
                    FStarC_Syntax_Syntax.ret_opt = asc_opt1;
                    FStarC_Syntax_Syntax.brs = bs1;
                    FStarC_Syntax_Syntax.rc_opt1 = ropt1;_},
                  FStarC_Syntax_Syntax.Tm_match
                  { FStarC_Syntax_Syntax.scrutinee = t21;
                    FStarC_Syntax_Syntax.ret_opt = asc_opt2;
                    FStarC_Syntax_Syntax.brs = bs2;
                    FStarC_Syntax_Syntax.rc_opt1 = ropt2;_})
                   ->
                   (((equal_term t11 t21) &&
                       (equal_opt equal_match_returns asc_opt1 asc_opt2))
                      && (equal_list equal_branch bs1 bs2))
                     && (equal_opt equal_rc ropt1 ropt2)
               | (FStarC_Syntax_Syntax.Tm_ascribed
                  { FStarC_Syntax_Syntax.tm = t11;
                    FStarC_Syntax_Syntax.asc = a1;
                    FStarC_Syntax_Syntax.eff_opt = l1;_},
                  FStarC_Syntax_Syntax.Tm_ascribed
                  { FStarC_Syntax_Syntax.tm = t21;
                    FStarC_Syntax_Syntax.asc = a2;
                    FStarC_Syntax_Syntax.eff_opt = l2;_})
                   ->
                   ((equal_term t11 t21) && (equal_ascription a1 a2)) &&
                     (equal_opt FStarC_Ident.lid_equals l1 l2)
               | (FStarC_Syntax_Syntax.Tm_let
                  { FStarC_Syntax_Syntax.lbs = (r1, lbs1);
                    FStarC_Syntax_Syntax.body1 = t11;_},
                  FStarC_Syntax_Syntax.Tm_let
                  { FStarC_Syntax_Syntax.lbs = (r2, lbs2);
                    FStarC_Syntax_Syntax.body1 = t21;_})
                   ->
                   ((r1 = r2) && (equal_list equal_letbinding lbs1 lbs2)) &&
                     (equal_term t11 t21)
               | (FStarC_Syntax_Syntax.Tm_uvar u1,
                  FStarC_Syntax_Syntax.Tm_uvar u2) -> equal_uvar u1 u2
               | (FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t11;
                    FStarC_Syntax_Syntax.meta = m1;_},
                  FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t21;
                    FStarC_Syntax_Syntax.meta = m2;_})
                   -> (equal_term t11 t21) && (equal_meta m1 m2)
               | (FStarC_Syntax_Syntax.Tm_lazy l1,
                  FStarC_Syntax_Syntax.Tm_lazy l2) -> equal_lazyinfo l1 l2
               | (FStarC_Syntax_Syntax.Tm_quoted (t11, q1),
                  FStarC_Syntax_Syntax.Tm_quoted (t21, q2)) ->
                   (equal_term t11 t21) && (equal_quoteinfo q1 q2)
               | (FStarC_Syntax_Syntax.Tm_unknown,
                  FStarC_Syntax_Syntax.Tm_unknown) -> true
               | uu___7 -> false)))
and (equal_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun c1 ->
    fun c2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality c1 c2 in
      if uu___
      then true
      else
        (match ((c1.FStarC_Syntax_Syntax.n), (c2.FStarC_Syntax_Syntax.n))
         with
         | (FStarC_Syntax_Syntax.Total t1, FStarC_Syntax_Syntax.Total t2) ->
             equal_term t1 t2
         | (FStarC_Syntax_Syntax.GTotal t1, FStarC_Syntax_Syntax.GTotal t2)
             -> equal_term t1 t2
         | (FStarC_Syntax_Syntax.Comp ct1, FStarC_Syntax_Syntax.Comp ct2) ->
             ((((FStarC_Ident.lid_equals ct1.FStarC_Syntax_Syntax.effect_name
                   ct2.FStarC_Syntax_Syntax.effect_name)
                  &&
                  (equal_list equal_universe
                     ct1.FStarC_Syntax_Syntax.comp_univs
                     ct2.FStarC_Syntax_Syntax.comp_univs))
                 &&
                 (equal_term ct1.FStarC_Syntax_Syntax.result_typ
                    ct2.FStarC_Syntax_Syntax.result_typ))
                &&
                (equal_list equal_arg ct1.FStarC_Syntax_Syntax.effect_args
                   ct2.FStarC_Syntax_Syntax.effect_args))
               &&
               (equal_list equal_flag ct1.FStarC_Syntax_Syntax.flags
                  ct2.FStarC_Syntax_Syntax.flags))
and (equal_binder :
  FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.binder -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality b1 b2 in
      if uu___
      then true
      else
        ((equal_bv b1.FStarC_Syntax_Syntax.binder_bv
            b2.FStarC_Syntax_Syntax.binder_bv)
           &&
           (equal_bqual b1.FStarC_Syntax_Syntax.binder_qual
              b2.FStarC_Syntax_Syntax.binder_qual))
          &&
          (equal_list equal_term b1.FStarC_Syntax_Syntax.binder_attrs
             b2.FStarC_Syntax_Syntax.binder_attrs)
and (equal_match_returns :
  (FStarC_Syntax_Syntax.binder *
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option * Prims.bool))
    ->
    (FStarC_Syntax_Syntax.binder *
      ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
      Prims.bool)) -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((b1, asc1), (b2, asc2)) ->
          (equal_binder b1 b2) && (equal_ascription asc1 asc2)
and (equal_ascription :
  ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
    FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option * Prims.bool)
    ->
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
      FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
      Prims.bool) -> Prims.bool)
  =
  fun x1 ->
    fun x2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality x1 x2 in
      if uu___
      then true
      else
        (let uu___2 = x1 in
         match uu___2 with
         | (a1, t1, b1) ->
             let uu___3 = x2 in
             (match uu___3 with
              | (a2, t2, b2) ->
                  ((match (a1, a2) with
                    | (FStar_Pervasives.Inl t11, FStar_Pervasives.Inl t21) ->
                        equal_term t11 t21
                    | (FStar_Pervasives.Inr c1, FStar_Pervasives.Inr c2) ->
                        equal_comp c1 c2
                    | uu___4 -> false) && (equal_opt equal_term t1 t2)) &&
                    (b1 = b2)))
and (equal_letbinding :
  FStarC_Syntax_Syntax.letbinding ->
    FStarC_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality l1 l2 in
      if uu___
      then true
      else
        (((((equal_lbname l1.FStarC_Syntax_Syntax.lbname
               l2.FStarC_Syntax_Syntax.lbname)
              &&
              (equal_list FStarC_Ident.ident_equals
                 l1.FStarC_Syntax_Syntax.lbunivs
                 l2.FStarC_Syntax_Syntax.lbunivs))
             &&
             (equal_term l1.FStarC_Syntax_Syntax.lbtyp
                l2.FStarC_Syntax_Syntax.lbtyp))
            &&
            (FStarC_Ident.lid_equals l1.FStarC_Syntax_Syntax.lbeff
               l2.FStarC_Syntax_Syntax.lbeff))
           &&
           (equal_term l1.FStarC_Syntax_Syntax.lbdef
              l2.FStarC_Syntax_Syntax.lbdef))
          &&
          (equal_list equal_term l1.FStarC_Syntax_Syntax.lbattrs
             l2.FStarC_Syntax_Syntax.lbattrs)
and (equal_uvar :
  (FStarC_Syntax_Syntax.ctx_uvar * (FStarC_Syntax_Syntax.subst_elt Prims.list
    Prims.list * FStarC_Syntax_Syntax.maybe_set_use_range)) ->
    (FStarC_Syntax_Syntax.ctx_uvar * (FStarC_Syntax_Syntax.subst_elt
      Prims.list Prims.list * FStarC_Syntax_Syntax.maybe_set_use_range)) ->
      Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((u1, (s1, uu___2)), (u2, (s2, uu___3))) ->
          (FStarC_Syntax_Unionfind.equiv
             u1.FStarC_Syntax_Syntax.ctx_uvar_head
             u2.FStarC_Syntax_Syntax.ctx_uvar_head)
            && (equal_list (equal_list equal_subst_elt) s1 s2)
and (equal_bv :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.bv -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality b1 b2 in
      if uu___
      then true
      else
        (FStarC_Ident.ident_equals b1.FStarC_Syntax_Syntax.ppname
           b2.FStarC_Syntax_Syntax.ppname)
          &&
          (equal_term b1.FStarC_Syntax_Syntax.sort
             b2.FStarC_Syntax_Syntax.sort)
and (equal_fv :
  FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.fv -> Prims.bool) =
  fun f1 ->
    fun f2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality f1 f2 in
      if uu___
      then true
      else
        FStarC_Ident.lid_equals
          (f1.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
          (f2.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
and (equal_universe :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1 ->
    fun u2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality u1 u2 in
      if uu___
      then true
      else
        (let uu___2 =
           let uu___3 = FStarC_Syntax_Subst.compress_univ u1 in
           let uu___4 = FStarC_Syntax_Subst.compress_univ u2 in
           (uu___3, uu___4) in
         match uu___2 with
         | (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_zero) -> true
         | (FStarC_Syntax_Syntax.U_succ u11, FStarC_Syntax_Syntax.U_succ u21)
             -> equal_universe u11 u21
         | (FStarC_Syntax_Syntax.U_max us1, FStarC_Syntax_Syntax.U_max us2)
             -> equal_list equal_universe us1 us2
         | (FStarC_Syntax_Syntax.U_bvar i1, FStarC_Syntax_Syntax.U_bvar i2)
             -> i1 = i2
         | (FStarC_Syntax_Syntax.U_name x1, FStarC_Syntax_Syntax.U_name x2)
             -> FStarC_Ident.ident_equals x1 x2
         | (FStarC_Syntax_Syntax.U_unif u11, FStarC_Syntax_Syntax.U_unif u21)
             -> FStarC_Syntax_Unionfind.univ_equiv u11 u21
         | (FStarC_Syntax_Syntax.U_unknown, FStarC_Syntax_Syntax.U_unknown)
             -> true
         | uu___3 -> false)
and (equal_constant :
  FStarC_Syntax_Syntax.sconst -> FStarC_Syntax_Syntax.sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality c1 c2 in
      if uu___
      then true
      else
        (match (c1, c2) with
         | (FStarC_Const.Const_effect, FStarC_Const.Const_effect) -> true
         | (FStarC_Const.Const_unit, FStarC_Const.Const_unit) -> true
         | (FStarC_Const.Const_bool b1, FStarC_Const.Const_bool b2) ->
             b1 = b2
         | (FStarC_Const.Const_int (s1, o1), FStarC_Const.Const_int (s2, o2))
             -> (s1 = s2) && (o1 = o2)
         | (FStarC_Const.Const_char c11, FStarC_Const.Const_char c21) ->
             c11 = c21
         | (FStarC_Const.Const_real s1, FStarC_Const.Const_real s2) ->
             s1 = s2
         | (FStarC_Const.Const_string (s1, uu___2), FStarC_Const.Const_string
            (s2, uu___3)) -> s1 = s2
         | (FStarC_Const.Const_range_of, FStarC_Const.Const_range_of) -> true
         | (FStarC_Const.Const_set_range_of, FStarC_Const.Const_set_range_of)
             -> true
         | (FStarC_Const.Const_range r1, FStarC_Const.Const_range r2) ->
             let uu___2 = FStarC_Compiler_Range_Ops.compare r1 r2 in
             uu___2 = Prims.int_zero
         | (FStarC_Const.Const_reify uu___2, FStarC_Const.Const_reify uu___3)
             -> true
         | (FStarC_Const.Const_reflect l1, FStarC_Const.Const_reflect l2) ->
             FStarC_Ident.lid_equals l1 l2
         | uu___2 -> false)
and (equal_arg :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
    FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      Prims.bool)
  =
  fun arg1 ->
    fun arg2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality arg1 arg2 in
      if uu___
      then true
      else
        (let uu___2 = arg1 in
         match uu___2 with
         | (t1, a1) ->
             let uu___3 = arg2 in
             (match uu___3 with
              | (t2, a2) ->
                  (equal_term t1 t2) && (equal_opt equal_arg_qualifier a1 a2)))
and (equal_bqual :
  FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.binder_qualifier FStar_Pervasives_Native.option ->
      Prims.bool)
  = fun b1 -> fun b2 -> equal_opt equal_binder_qualifier b1 b2
and (equal_binder_qualifier :
  FStarC_Syntax_Syntax.binder_qualifier ->
    FStarC_Syntax_Syntax.binder_qualifier -> Prims.bool)
  =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStarC_Syntax_Syntax.Implicit b11, FStarC_Syntax_Syntax.Implicit
         b21) -> b11 = b21
      | (FStarC_Syntax_Syntax.Equality, FStarC_Syntax_Syntax.Equality) ->
          true
      | (FStarC_Syntax_Syntax.Meta t1, FStarC_Syntax_Syntax.Meta t2) ->
          equal_term t1 t2
      | uu___ -> false
and (equal_branch :
  (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
    FStarC_Syntax_Syntax.syntax) ->
    (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
      FStarC_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun uu___ ->
    fun uu___1 ->
      match (uu___, uu___1) with
      | ((p1, w1, t1), (p2, w2, t2)) ->
          ((equal_pat p1 p2) && (equal_opt equal_term w1 w2)) &&
            (equal_term t1 t2)
and (equal_pat :
  FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t ->
    FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t -> Prims.bool)
  =
  fun p1 ->
    fun p2 ->
      let uu___ = FStarC_Compiler_Util.physical_equality p1 p2 in
      if uu___
      then true
      else
        (match ((p1.FStarC_Syntax_Syntax.v), (p2.FStarC_Syntax_Syntax.v))
         with
         | (FStarC_Syntax_Syntax.Pat_constant c1,
            FStarC_Syntax_Syntax.Pat_constant c2) -> equal_constant c1 c2
         | (FStarC_Syntax_Syntax.Pat_cons (fv1, us1, args1),
            FStarC_Syntax_Syntax.Pat_cons (fv2, us2, args2)) ->
             ((equal_fv fv1 fv2) &&
                (equal_opt (equal_list equal_universe) us1 us2))
               && (equal_list (equal_pair equal_pat equal_poly) args1 args2)
         | (FStarC_Syntax_Syntax.Pat_var bv1, FStarC_Syntax_Syntax.Pat_var
            bv2) -> equal_bv bv1 bv2
         | (FStarC_Syntax_Syntax.Pat_dot_term t1,
            FStarC_Syntax_Syntax.Pat_dot_term t2) ->
             equal_opt equal_term t1 t2
         | uu___2 -> false)
and (equal_meta :
  FStarC_Syntax_Syntax.metadata ->
    FStarC_Syntax_Syntax.metadata -> Prims.bool)
  =
  fun m1 ->
    fun m2 ->
      match (m1, m2) with
      | (FStarC_Syntax_Syntax.Meta_pattern (ts1, args1),
         FStarC_Syntax_Syntax.Meta_pattern (ts2, args2)) ->
          (equal_list equal_term ts1 ts2) &&
            (equal_list (equal_list equal_arg) args1 args2)
      | (FStarC_Syntax_Syntax.Meta_named l1, FStarC_Syntax_Syntax.Meta_named
         l2) -> FStarC_Ident.lid_equals l1 l2
      | (FStarC_Syntax_Syntax.Meta_labeled (s1, r1, uu___),
         FStarC_Syntax_Syntax.Meta_labeled (s2, r2, uu___1)) ->
          (s1 = s2) &&
            (let uu___2 = FStarC_Compiler_Range_Ops.compare r1 r2 in
             uu___2 = Prims.int_zero)
      | (FStarC_Syntax_Syntax.Meta_desugared msi1,
         FStarC_Syntax_Syntax.Meta_desugared msi2) -> msi1 = msi2
      | (FStarC_Syntax_Syntax.Meta_monadic (m11, t1),
         FStarC_Syntax_Syntax.Meta_monadic (m21, t2)) ->
          (FStarC_Ident.lid_equals m11 m21) && (equal_term t1 t2)
      | (FStarC_Syntax_Syntax.Meta_monadic_lift (m11, n1, t1),
         FStarC_Syntax_Syntax.Meta_monadic_lift (m21, n2, t2)) ->
          ((FStarC_Ident.lid_equals m11 m21) &&
             (FStarC_Ident.lid_equals n1 n2))
            && (equal_term t1 t2)
and (equal_lazyinfo :
  FStarC_Syntax_Syntax.lazyinfo ->
    FStarC_Syntax_Syntax.lazyinfo -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      FStarC_Compiler_Util.physical_equality l1.FStarC_Syntax_Syntax.blob
        l2.FStarC_Syntax_Syntax.blob
and (equal_quoteinfo :
  FStarC_Syntax_Syntax.quoteinfo ->
    FStarC_Syntax_Syntax.quoteinfo -> Prims.bool)
  =
  fun q1 ->
    fun q2 ->
      ((q1.FStarC_Syntax_Syntax.qkind = q2.FStarC_Syntax_Syntax.qkind) &&
         ((FStar_Pervasives_Native.fst q1.FStarC_Syntax_Syntax.antiquotations)
            =
            (FStar_Pervasives_Native.fst
               q2.FStarC_Syntax_Syntax.antiquotations)))
        &&
        (equal_list equal_term
           (FStar_Pervasives_Native.snd
              q1.FStarC_Syntax_Syntax.antiquotations)
           (FStar_Pervasives_Native.snd
              q2.FStarC_Syntax_Syntax.antiquotations))
and (equal_rc :
  FStarC_Syntax_Syntax.residual_comp ->
    FStarC_Syntax_Syntax.residual_comp -> Prims.bool)
  =
  fun r1 ->
    fun r2 ->
      ((FStarC_Ident.lid_equals r1.FStarC_Syntax_Syntax.residual_effect
          r2.FStarC_Syntax_Syntax.residual_effect)
         &&
         (equal_opt equal_term r1.FStarC_Syntax_Syntax.residual_typ
            r2.FStarC_Syntax_Syntax.residual_typ))
        &&
        (equal_list equal_flag r1.FStarC_Syntax_Syntax.residual_flags
           r2.FStarC_Syntax_Syntax.residual_flags)
and (equal_flag :
  FStarC_Syntax_Syntax.cflag -> FStarC_Syntax_Syntax.cflag -> Prims.bool) =
  fun f1 ->
    fun f2 ->
      match (f1, f2) with
      | (FStarC_Syntax_Syntax.DECREASES t1, FStarC_Syntax_Syntax.DECREASES
         t2) -> equal_decreases_order t1 t2
      | uu___ -> f1 = f2
and (equal_decreases_order :
  FStarC_Syntax_Syntax.decreases_order ->
    FStarC_Syntax_Syntax.decreases_order -> Prims.bool)
  =
  fun d1 ->
    fun d2 ->
      match (d1, d2) with
      | (FStarC_Syntax_Syntax.Decreases_lex ts1,
         FStarC_Syntax_Syntax.Decreases_lex ts2) ->
          equal_list equal_term ts1 ts2
      | (FStarC_Syntax_Syntax.Decreases_wf (t1, t1'),
         FStarC_Syntax_Syntax.Decreases_wf (t2, t2')) ->
          (equal_term t1 t2) && (equal_term t1' t2')
and (equal_arg_qualifier :
  FStarC_Syntax_Syntax.arg_qualifier ->
    FStarC_Syntax_Syntax.arg_qualifier -> Prims.bool)
  =
  fun a1 ->
    fun a2 ->
      (a1.FStarC_Syntax_Syntax.aqual_implicit =
         a2.FStarC_Syntax_Syntax.aqual_implicit)
        &&
        (equal_list equal_term a1.FStarC_Syntax_Syntax.aqual_attributes
           a2.FStarC_Syntax_Syntax.aqual_attributes)
and (equal_lbname :
  (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv) FStar_Pervasives.either
    ->
    (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv)
      FStar_Pervasives.either -> Prims.bool)
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | (FStar_Pervasives.Inl b1, FStar_Pervasives.Inl b2) ->
          FStarC_Ident.ident_equals b1.FStarC_Syntax_Syntax.ppname
            b2.FStarC_Syntax_Syntax.ppname
      | (FStar_Pervasives.Inr f1, FStar_Pervasives.Inr f2) ->
          FStarC_Ident.lid_equals
            (f1.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
            (f2.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
and (equal_subst_elt :
  FStarC_Syntax_Syntax.subst_elt ->
    FStarC_Syntax_Syntax.subst_elt -> Prims.bool)
  =
  fun s1 ->
    fun s2 ->
      match (s1, s2) with
      | (FStarC_Syntax_Syntax.DB (i1, bv1), FStarC_Syntax_Syntax.DB
         (i2, bv2)) -> (i1 = i2) && (equal_bv bv1 bv2)
      | (FStarC_Syntax_Syntax.NM (bv1, i1), FStarC_Syntax_Syntax.NM
         (bv2, i2)) -> (i1 = i2) && (equal_bv bv1 bv2)
      | (FStarC_Syntax_Syntax.NT (bv1, t1), FStarC_Syntax_Syntax.NT
         (bv2, t2)) -> (equal_bv bv1 bv2) && (equal_term t1 t2)
      | (FStarC_Syntax_Syntax.UN (i1, u1), FStarC_Syntax_Syntax.UN (i2, u2))
          -> (i1 = i2) && (equal_universe u1 u2)
      | (FStarC_Syntax_Syntax.UD (un1, i1), FStarC_Syntax_Syntax.UD
         (un2, i2)) -> (i1 = i2) && (FStarC_Ident.ident_equals un1 un2)
let (hashable_term :
  FStarC_Syntax_Syntax.term FStarC_Class_Hashable.hashable) =
  { FStarC_Class_Hashable.hash = ext_hash_term }