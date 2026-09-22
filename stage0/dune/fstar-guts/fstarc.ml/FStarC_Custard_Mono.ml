open Prims
type bclass =
  | Mono 
  | Poly 
  | Dropped 
let uu___is_Mono (projectee : bclass) : Prims.bool=
  match projectee with | Mono -> true | uu___ -> false
let uu___is_Poly (projectee : bclass) : Prims.bool=
  match projectee with | Poly -> true | uu___ -> false
let uu___is_Dropped (projectee : bclass) : Prims.bool=
  match projectee with | Dropped -> true | uu___ -> false
let chain_reporter :
  (unit -> FStar_Pprint.document Prims.list) FStarC_Effect.ref=
  FStarC_Effect.mk_ref (fun uu___ -> [])
let norm_bounded (env : FStarC_TypeChecker_Env.env) (what : Prims.string)
  (steps : FStarC_TypeChecker_Env.step Prims.list)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ=
  try
    (fun uu___ ->
       match () with
       | () ->
           FStarC_Custard_Prof.timed "Mono.norm"
             (fun uu___1 ->
                let uu___2 = FStarC_Options.custard_norm_budget () in
                FStarC_TypeChecker_Normalize.with_budget uu___2
                  (fun uu___3 ->
                     FStarC_TypeChecker_Normalize.normalize steps env t))) ()
  with
  | FStarC_TypeChecker_Normalize.Budget_exceeded ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStarC_Options.custard_norm_budget () in
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int
                    uu___7 in
                Prims.strcat uu___6
                  (Prims.strcat " reduction steps) while normalizing "
                     (Prims.strcat what ".")) in
              Prims.strcat "Custard exceeded --custard_norm_budget (" uu___5 in
            FStar_Pprint.arbitrary_string uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  FStarC_Syntax_Print.term_to_string'
                    (FStarC_TypeChecker_Env.dsenv env) t in
                Prims.strcat
                  "The term being normalized, before reduction, was: " uu___7 in
              FStar_Pprint.arbitrary_string uu___6 in
            [uu___5] in
          uu___3 :: uu___4 in
        let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang chain_reporter in uu___4 () in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_CustardFuelExhausted ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___1)
let rec strip_aux (fuel : Prims.int) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  let t1 = FStarC_Syntax_Subst.compress t in
  if fuel <= Prims.int_zero
  then t1
  else
    (match t1.FStarC_Syntax_Syntax.n with
     | FStarC_Syntax_Syntax.Tm_ascribed uu___ ->
         let uu___1 = FStarC_Syntax_Util.unascribe t1 in
         strip_aux (fuel - Prims.int_one) uu___1
     | FStarC_Syntax_Syntax.Tm_refine uu___ ->
         let uu___1 = FStarC_Syntax_Util.unrefine t1 in
         strip_aux (fuel - Prims.int_one) uu___1
     | uu___ -> t1)
let strip (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ=
  strip_aux (Prims.of_int 16) t
let bclass_to_string (c : bclass) : Prims.string=
  match c with | Mono -> "Mono" | Poly -> "Poly" | Dropped -> "Dropped"
let showable_bclass : bclass FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = bclass_to_string }
let is_tcresolve_binder (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  match b.FStarC_Syntax_Syntax.binder_qual with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
      let uu___ = FStarC_Syntax_Util.head_and_args_full t in
      (match uu___ with
       | (hd, uu___1) ->
           FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid hd)
  | uu___ -> false
let is_tcclass_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Syntax_Subst.compress
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      FStarC_Syntax_Util.unrefine uu___2 in
    FStarC_Syntax_Util.head_and_args_full uu___1 in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_TypeChecker_Env.fv_has_attr env fv
             FStarC_Parser_Const.tcclass_lid
       | uu___3 -> false)
let is_unspecializable_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Syntax_Subst.compress
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      FStarC_Syntax_Util.unrefine uu___2 in
    FStarC_Syntax_Util.head_and_args_full uu___1 in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_TypeChecker_Env.fv_has_attr env fv
             FStarC_Parser_Const.custard_no_monomorphize_attr
       | uu___3 -> false)
let rec is_arity_aux (normed : Prims.bool) (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let t1 = strip t in
  match t1.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_type uu___ -> true
  | FStarC_Syntax_Syntax.Tm_arrow uu___ ->
      let uu___1 = FStarC_Syntax_Util.arrow_formals_comp t1 in
      (match uu___1 with
       | (bs, c) ->
           let uu___2 = FStarC_TypeChecker_Env.push_binders env bs in
           is_arity_aux false uu___2 (FStarC_Syntax_Util.comp_result c))
  | FStarC_Syntax_Syntax.Tm_fvar uu___ ->
      if Prims.not normed
      then
        let uu___1 =
          norm_bounded env "a binder's sort"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t1 in
        is_arity_aux true env uu___1
      else false
  | FStarC_Syntax_Syntax.Tm_app uu___ ->
      if Prims.not normed
      then
        let uu___1 =
          norm_bounded env "a binder's sort"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t1 in
        is_arity_aux true env uu___1
      else false
  | FStarC_Syntax_Syntax.Tm_uinst uu___ ->
      if Prims.not normed
      then
        let uu___1 =
          norm_bounded env "a binder's sort"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t1 in
        is_arity_aux true env uu___1
      else false
  | uu___ -> false
let is_arity (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  FStarC_Custard_Prof.timed "Mono.is_arity"
    (fun uu___ -> is_arity_aux false env t)
let is_type_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  is_arity env (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
let rec is_star_aux (normed : Prims.bool) (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = let uu___1 = strip t in uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_fvar uu___1 ->
      if Prims.not normed
      then
        let uu___2 =
          norm_bounded env "a binder's kind"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t in
        is_star_aux true env uu___2
      else false
  | FStarC_Syntax_Syntax.Tm_app uu___1 ->
      if Prims.not normed
      then
        let uu___2 =
          norm_bounded env "a binder's kind"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t in
        is_star_aux true env uu___2
      else false
  | FStarC_Syntax_Syntax.Tm_uinst uu___1 ->
      if Prims.not normed
      then
        let uu___2 =
          norm_bounded env "a binder's kind"
            [FStarC_TypeChecker_Env.AllowUnboundUniverses;
            FStarC_TypeChecker_Env.EraseUniverses;
            FStarC_TypeChecker_Env.Beta;
            FStarC_TypeChecker_Env.Iota;
            FStarC_TypeChecker_Env.Weak;
            FStarC_TypeChecker_Env.HNF;
            FStarC_TypeChecker_Env.UnfoldUntil
              FStarC_Syntax_Syntax.delta_constant] t in
        is_star_aux true env uu___2
      else false
  | uu___1 -> false
let is_value_indexed_arity (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.arrow_formals t in
  match uu___ with
  | (bs, res) ->
      let uu___1 =
        if match bs with | hd::tl -> true | uu___2 -> false
        then is_star_aux false env res
        else false in
      if uu___1
      then
        FStarC_List.for_all
          (fun b ->
             let uu___2 =
               is_arity env
                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
             Prims.not uu___2) bs
      else false
let is_type_param (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let uu___ =
    is_star_aux false env
      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
  if uu___
  then true
  else
    is_value_indexed_arity env
      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
let is_dropped_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let sort = (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.is_exactly_unit sort in
      Prims.not uu___2 in
    if uu___1
    then let uu___2 = is_type_binder env b in Prims.not uu___2
    else false in
  if uu___
  then
    FStarC_Custard_Prof.timed "Mono.must_erase"
      (fun uu___1 ->
         FStarC_TypeChecker_Util.must_erase_for_extraction env sort)
  else false
let is_unit_binder (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  FStarC_Syntax_Util.is_unit
    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
let rec is_type_term (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_type uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_arrow uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_refine uu___1 -> true
  | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_type_term env t1
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = uu___1;
        FStarC_Syntax_Syntax.eff_opt = uu___2;_}
      -> is_type_term env t1
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = uu___1;_}
      -> is_type_term env t1
  | FStarC_Syntax_Syntax.Tm_name bv ->
      is_arity env bv.FStarC_Syntax_Syntax.sort
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let uu___1 =
        FStarC_TypeChecker_Env.try_lookup_lid env
          (FStarC_Syntax_Syntax.lid_of_fv fv) in
      (match uu___1 with
       | FStar_Pervasives_Native.Some ((uu___2, ty), uu___3) ->
           is_arity env ty
       | FStar_Pervasives_Native.None -> false)
  | FStarC_Syntax_Syntax.Tm_app uu___1 ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.head_and_args_full t in
        FStar_Pervasives_Native.fst uu___3 in
      is_type_term env uu___2
  | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
      let uu___2 = FStarC_Syntax_Util.abs_formals t in
      (match uu___2 with
       | (bs, body, uu___3) ->
           let uu___4 = FStarC_TypeChecker_Env.push_binders env bs in
           is_type_term uu___4 body)
  | uu___1 -> false
let is_erased_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let uu___ = is_type_binder env b in
  if uu___ then true else is_dropped_binder env b
let is_erased_term (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = is_type_term env t in
  if uu___
  then true
  else
    (let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Syntax_Util.unascribe t in
         FStarC_Syntax_Subst.compress uu___3 in
       uu___2.FStarC_Syntax_Syntax.n in
     match uu___1 with
     | FStarC_Syntax_Syntax.Tm_name bv ->
         is_dropped_binder env (FStarC_Syntax_Syntax.mk_binder bv)
     | uu___2 -> false)
let classes_to_string (env : FStarC_TypeChecker_Env.env)
  (bs : FStarC_Syntax_Syntax.binders) (cs : bclass Prims.list) :
  Prims.string=
  let why b =
    let uu___ = is_type_binder env b in
    if uu___
    then "type"
    else
      (let uu___1 = is_unit_binder b in
       if uu___1
       then "unit"
       else
         (let uu___2 = is_dropped_binder env b in
          if uu___2 then "erased" else "?")) in
  let rec go bs1 cs1 =
    match (bs1, cs1) with
    | ([], []) -> []
    | (b::bs2, []) ->
        let uu___ =
          let uu___1 = let uu___2 = why b in Prims.strcat uu___2 ">" in
          Prims.strcat "<" uu___1 in
        let uu___1 = go bs2 [] in uu___ :: uu___1
    | ([], c::cs2) -> let uu___ = go [] cs2 in (bclass_to_string c) :: uu___
    | (b::bs2, c::cs2) ->
        let uu___ =
          match c with
          | Dropped -> let uu___1 = why b in Prims.strcat "Dropped:" uu___1
          | c1 -> bclass_to_string c1 in
        let uu___1 = go bs2 cs2 in uu___ :: uu___1 in
  let uu___ = go bs cs in FStarC_String.concat "; " uu___
let impure_codomain (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Syntax_Util.is_pure_or_ghost_comp c in
    Prims.not uu___1 in
  if uu___
  then true
  else
    (let uu___1 =
       FStarC_Custard_Effects.impure_effect_result env
         (FStarC_Syntax_Util.comp_result c) in
     match uu___1 with
     | FStar_Pervasives_Native.Some v -> true
     | uu___2 -> false)
let keep_thunk (env : FStarC_TypeChecker_Env.env)
  (bs : FStarC_Syntax_Syntax.binders) (c : FStarC_Syntax_Syntax.comp)
  (flags : Prims.bool Prims.list) : Prims.bool Prims.list=
  let last l =
    match FStarC_List.rev l with
    | x::uu___ -> FStar_Pervasives_Native.Some x
    | [] -> FStar_Pervasives_Native.None in
  let becomes_value =
    if match flags with | hd::tl -> true | uu___ -> false
    then FStarC_List.for_all (fun b -> b) flags
    else false in
  let last_explicit =
    let uu___ = last bs in
    match uu___ with
    | FStar_Pervasives_Native.Some b ->
        Prims.not
          (FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
             b.FStarC_Syntax_Syntax.binder_qual)
    | FStar_Pervasives_Native.None -> false in
  let is_thunk =
    let uu___ = impure_codomain env c in
    if uu___ then last_explicit else false in
  let uu___ =
    let uu___1 =
      let uu___2 = last flags in uu___2 = (FStar_Pervasives_Native.Some true) in
    if uu___1 then becomes_value || is_thunk else false in
  if uu___
  then
    match FStarC_List.rev flags with
    | uu___1::rest -> FStarC_List.rev (false :: rest)
    | [] -> flags
  else flags
let erased_binders (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool Prims.list=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t in
  match uu___ with
  | (bs, uu___1) -> FStarC_List.map (is_erased_binder env) bs
let rec arrow_formals_unfold_aux (fuel : Prims.int)
  (env : FStarC_TypeChecker_Env.env) (t : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp)=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t in
  match uu___ with
  | (bs, c) ->
      let uu___1 =
        if fuel <= Prims.int_zero
        then true
        else
          (let uu___2 = FStarC_Syntax_Util.is_total_comp c in
           Prims.not uu___2) in
      if uu___1
      then (bs, c)
      else
        (let env1 = FStarC_TypeChecker_Env.push_binders env bs in
         let r =
           norm_bounded env1 "an arrow spine"
             [FStarC_TypeChecker_Env.AllowUnboundUniverses;
             FStarC_TypeChecker_Env.EraseUniverses;
             FStarC_TypeChecker_Env.Beta;
             FStarC_TypeChecker_Env.Weak;
             FStarC_TypeChecker_Env.HNF;
             FStarC_TypeChecker_Env.UnfoldUntil
               FStarC_Syntax_Syntax.delta_constant]
             (FStarC_Syntax_Util.comp_result c) in
         let r1 = strip r in
         match r1.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Tm_arrow uu___2 ->
             let uu___3 =
               arrow_formals_unfold_aux (fuel - Prims.int_one) env1 r1 in
             (match uu___3 with
              | (bs', c') -> ((FStarC_List.op_At bs bs'), c'))
         | uu___2 -> (bs, c))
let arrow_formals_unfold (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp)=
  FStarC_Custard_Prof.timed "Mono.arrow_formals_unfold"
    (fun uu___ -> arrow_formals_unfold_aux (Prims.of_int 8) env t)
let erased_binders_unfold (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool Prims.list=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with
  | (bs, c) ->
      let uu___1 = FStarC_List.map (is_erased_binder env) bs in
      keep_thunk env bs c uu___1
let retained_binders (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.binders=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with
  | (bs, c) ->
      let flags =
        let uu___1 = FStarC_List.map (is_erased_binder env) bs in
        keep_thunk env bs c uu___1 in
      let uu___1 =
        FStarC_List.filter
          (fun uu___2 ->
             match uu___2 with | (uu___3, dropped) -> Prims.not dropped)
          (FStarC_List.zip bs flags) in
      FStarC_List.map FStar_Pervasives_Native.fst uu___1
let retained_sorts (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ Prims.list=
  let uu___ = retained_binders env t in
  FStarC_List.map
    (fun b -> (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
    uu___
let retained_names (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.string Prims.list=
  let uu___ = retained_binders env t in
  FStarC_List.map
    (fun b ->
       FStarC_Ident.string_of_id
         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
    uu___
let unit_binders (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool Prims.list=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with
  | (bs, uu___1) ->
      FStarC_List.map
        (fun b ->
           let uu___2 =
             FStarC_Syntax_Util.is_unit
               (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
           if uu___2 then true else is_erased_binder env b) bs
let type_binders (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool Prims.list=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with | (bs, uu___1) -> FStarC_List.map (is_type_binder env) bs
let type_params (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool Prims.list=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp t in
  match uu___ with | (bs, uu___1) -> FStarC_List.map (is_type_param env) bs
let ctor_stores_type (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let uu___ = FStarC_TypeChecker_Env.lookup_sigelt env l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      {
        FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
          { FStarC_Syntax_Syntax.lid1 = uu___1;
            FStarC_Syntax_Syntax.us1 = uu___2; FStarC_Syntax_Syntax.t1 = t;
            FStarC_Syntax_Syntax.ty_lid = uu___3;
            FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
            FStarC_Syntax_Syntax.mutuals1 = uu___4;
            FStarC_Syntax_Syntax.injective_type_params1 = uu___5;
            FStarC_Syntax_Syntax.proj_disc_lids = uu___6;_};
        FStarC_Syntax_Syntax.sigrng = uu___7;
        FStarC_Syntax_Syntax.sigquals = uu___8;
        FStarC_Syntax_Syntax.sigmeta = uu___9;
        FStarC_Syntax_Syntax.sigattrs = uu___10;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___11;
        FStarC_Syntax_Syntax.sigopts = uu___12;_}
      ->
      let uu___13 = FStarC_Syntax_Util.arrow_formals t in
      (match uu___13 with
       | (bs, uu___14) ->
           if (FStarC_List.length bs) <= num_ty_params
           then false
           else
             (let fields =
                FStar_Pervasives_Native.snd
                  (FStarC_List.splitAt num_ty_params bs) in
              let rec scan bs1 =
                match bs1 with
                | [] -> false
                | b::rest ->
                    let uu___15 =
                      let uu___16 =
                        FStarC_Syntax_Subst.compress
                          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                      uu___16.FStarC_Syntax_Syntax.n in
                    (match uu___15 with
                     | FStarC_Syntax_Syntax.Tm_type uu___16 ->
                         let uu___17 =
                           FStarC_List.existsb
                             (fun b2 ->
                                let uu___18 =
                                  let uu___19 =
                                    FStarC_Syntax_Free.names
                                      (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                  FStarC_Class_Setlike.elems
                                    (FStarC_FlatSet.setlike_flat_set
                                       FStarC_Syntax_Syntax.ord_bv) uu___19 in
                                FStarC_List.existsb
                                  (fun v ->
                                     FStarC_Syntax_Syntax.bv_eq v
                                       b.FStarC_Syntax_Syntax.binder_bv)
                                  uu___18) rest in
                         if uu___17 then true else scan rest
                     | uu___16 -> scan rest) in
              scan fields))
  | uu___1 -> false
let existential_of_lid (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) :
  (FStarC_Ident.lident * FStarC_Ident.lident) FStar_Pervasives_Native.option=
  let uu___ = FStarC_TypeChecker_Env.lookup_sigelt env l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      {
        FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
          { FStarC_Syntax_Syntax.lid = uu___1;
            FStarC_Syntax_Syntax.us = uu___2;
            FStarC_Syntax_Syntax.params = uu___3;
            FStarC_Syntax_Syntax.num_uniform_params = uu___4;
            FStarC_Syntax_Syntax.t = uu___5;
            FStarC_Syntax_Syntax.mutuals = uu___6;
            FStarC_Syntax_Syntax.ds = ds;
            FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
        FStarC_Syntax_Syntax.sigrng = uu___8;
        FStarC_Syntax_Syntax.sigquals = uu___9;
        FStarC_Syntax_Syntax.sigmeta = uu___10;
        FStarC_Syntax_Syntax.sigattrs = uu___11;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
        FStarC_Syntax_Syntax.sigopts = uu___13;_}
      ->
      let rec first ds1 =
        match ds1 with
        | [] -> FStar_Pervasives_Native.None
        | c::ds' ->
            let uu___14 =
              let uu___15 = ctor_stores_type env c in Prims.not uu___15 in
            if uu___14
            then first ds'
            else
              (let uu___15 = FStarC_TypeChecker_Env.lookup_sigelt env c in
               match uu___15 with
               | FStar_Pervasives_Native.Some
                   {
                     FStarC_Syntax_Syntax.sigel =
                       FStarC_Syntax_Syntax.Sig_datacon
                       { FStarC_Syntax_Syntax.lid1 = uu___16;
                         FStarC_Syntax_Syntax.us1 = uu___17;
                         FStarC_Syntax_Syntax.t1 = t;
                         FStarC_Syntax_Syntax.ty_lid = uu___18;
                         FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
                         FStarC_Syntax_Syntax.mutuals1 = uu___19;
                         FStarC_Syntax_Syntax.injective_type_params1 =
                           uu___20;
                         FStarC_Syntax_Syntax.proj_disc_lids = uu___21;_};
                     FStarC_Syntax_Syntax.sigrng = uu___22;
                     FStarC_Syntax_Syntax.sigquals = uu___23;
                     FStarC_Syntax_Syntax.sigmeta = uu___24;
                     FStarC_Syntax_Syntax.sigattrs = uu___25;
                     FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___26;
                     FStarC_Syntax_Syntax.sigopts = uu___27;_}
                   ->
                   let uu___28 = FStarC_Syntax_Util.arrow_formals t in
                   (match uu___28 with
                    | (bs, uu___29) ->
                        let fields =
                          if (FStarC_List.length bs) <= num_ty_params
                          then []
                          else
                            FStar_Pervasives_Native.snd
                              (FStarC_List.splitAt num_ty_params bs) in
                        let rec pick bs1 =
                          match bs1 with
                          | [] -> FStar_Pervasives_Native.None
                          | b::rest ->
                              let uu___30 =
                                let uu___31 =
                                  FStarC_Syntax_Subst.compress
                                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                uu___31.FStarC_Syntax_Syntax.n in
                              (match uu___30 with
                               | FStarC_Syntax_Syntax.Tm_type uu___31 when
                                   FStarC_List.existsb
                                     (fun b2 ->
                                        let uu___32 =
                                          let uu___33 =
                                            FStarC_Syntax_Free.names
                                              (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                          FStarC_Class_Setlike.elems
                                            (FStarC_FlatSet.setlike_flat_set
                                               FStarC_Syntax_Syntax.ord_bv)
                                            uu___33 in
                                        FStarC_List.existsb
                                          (fun v ->
                                             FStarC_Syntax_Syntax.bv_eq v
                                               b.FStarC_Syntax_Syntax.binder_bv)
                                          uu___32) rest
                                   ->
                                   let uu___32 =
                                     FStarC_Ident.lid_of_ids
                                       [(b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname] in
                                   FStar_Pervasives_Native.Some uu___32
                               | uu___31 -> pick rest) in
                        let uu___30 = pick fields in
                        (match uu___30 with
                         | FStar_Pervasives_Native.Some f ->
                             FStar_Pervasives_Native.Some (c, f)
                         | FStar_Pervasives_Native.None -> first ds'))
               | uu___16 -> first ds') in
      first ds
  | uu___1 -> FStar_Pervasives_Native.None
let existential_field (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) :
  (FStarC_Ident.lident * FStarC_Ident.lident) FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Syntax_Subst.compress
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      FStarC_Syntax_Util.unrefine uu___2 in
    FStarC_Syntax_Util.head_and_args_full uu___1 in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           existential_of_lid env (FStarC_Syntax_Syntax.lid_of_fv fv)
       | uu___3 -> FStar_Pervasives_Native.None)
let is_type_carrying_binder (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.binder) : Prims.bool=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Syntax_Subst.compress
          (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
      FStarC_Syntax_Util.unrefine uu___2 in
    FStarC_Syntax_Util.head_and_args_full uu___1 in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           let uu___3 =
             FStarC_TypeChecker_Env.lookup_sigelt env
               (FStarC_Syntax_Syntax.lid_of_fv fv) in
           (match uu___3 with
            | FStar_Pervasives_Native.Some
                {
                  FStarC_Syntax_Syntax.sigel =
                    FStarC_Syntax_Syntax.Sig_inductive_typ
                    { FStarC_Syntax_Syntax.lid = uu___4;
                      FStarC_Syntax_Syntax.us = uu___5;
                      FStarC_Syntax_Syntax.params = uu___6;
                      FStarC_Syntax_Syntax.num_uniform_params = uu___7;
                      FStarC_Syntax_Syntax.t = uu___8;
                      FStarC_Syntax_Syntax.mutuals = uu___9;
                      FStarC_Syntax_Syntax.ds = ds;
                      FStarC_Syntax_Syntax.injective_type_params = uu___10;_};
                  FStarC_Syntax_Syntax.sigrng = uu___11;
                  FStarC_Syntax_Syntax.sigquals = uu___12;
                  FStarC_Syntax_Syntax.sigmeta = uu___13;
                  FStarC_Syntax_Syntax.sigattrs = uu___14;
                  FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___15;
                  FStarC_Syntax_Syntax.sigopts = uu___16;_}
                -> FStarC_List.existsb (ctor_stores_type env) ds
            | uu___4 -> false)
       | uu___3 -> false)
let classify_demand (env : FStarC_TypeChecker_Env.env)
  (attrs : FStarC_Syntax_Syntax.attribute Prims.list)
  (t : FStarC_Syntax_Syntax.typ)
  (def : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (demanded : Prims.int Prims.list) : bclass Prims.list=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with
  | (bs, comp) ->
      let bs1 =
        match def with
        | FStar_Pervasives_Native.None -> bs
        | FStar_Pervasives_Native.Some d ->
            let uu___1 = FStarC_Syntax_Util.abs_formals d in
            (match uu___1 with
             | (bs_d, uu___2, uu___3) ->
                 FStarC_List.mapi
                   (fun i b ->
                      if i < (FStarC_List.length bs_d)
                      then
                        let bd = FStarC_List.nth bs_d i in
                        (if
                           match bd.FStarC_Syntax_Syntax.binder_attrs with
                           | [] -> true
                           | uu___4 -> false
                         then b
                         else
                           {
                             FStarC_Syntax_Syntax.binder_bv =
                               (b.FStarC_Syntax_Syntax.binder_bv);
                             FStarC_Syntax_Syntax.binder_qual =
                               (b.FStarC_Syntax_Syntax.binder_qual);
                             FStarC_Syntax_Syntax.binder_positivity =
                               (b.FStarC_Syntax_Syntax.binder_positivity);
                             FStarC_Syntax_Syntax.binder_attrs =
                               (FStarC_List.op_At
                                  b.FStarC_Syntax_Syntax.binder_attrs
                                  bd.FStarC_Syntax_Syntax.binder_attrs)
                           })
                      else b) bs) in
      let all_mono =
        FStarC_Syntax_Util.has_attribute attrs
          FStarC_Parser_Const.monomorphize_attr in
      let mono_types = FStarC_Options.custard_monomorphize_types () in
      let init i b =
        let uu___1 =
          let uu___2 = is_dropped_binder env b in
          if uu___2 then true else is_unit_binder b in
        if uu___1
        then Dropped
        else
          (let uu___2 =
             FStarC_Syntax_Util.has_attribute
               b.FStarC_Syntax_Syntax.binder_attrs
               FStarC_Parser_Const.monomorphize_attr in
           if uu___2
           then Mono
           else
             (let uu___3 = is_unspecializable_binder env b in
              if uu___3
              then Poly
              else
                (let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           if all_mono then true else is_tcresolve_binder b in
                         if uu___8 then true else is_tcclass_binder env b in
                       if uu___7
                       then true
                       else
                         if mono_types then is_type_binder env b else false in
                     if uu___6 then true else is_type_carrying_binder env b in
                   if uu___5 then true else FStarC_List.mem i demanded in
                 if uu___4 then Mono else Poly))) in
      let cs = FStarC_List.mapi init bs1 in
      let bcs = FStarC_List.zip bs1 cs in
      let pass bcs1 =
        let needed =
          FStarC_List.collect
            (fun uu___1 ->
               match uu___1 with
               | (b, c) ->
                   (match c with
                    | Mono ->
                        let uu___2 =
                          FStarC_Syntax_Free.names
                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        FStarC_Class_Setlike.elems
                          (FStarC_FlatSet.setlike_flat_set
                             FStarC_Syntax_Syntax.ord_bv) uu___2
                    | uu___2 -> [])) bcs1 in
        let changed = FStarC_Effect.mk_ref false in
        let bcs2 =
          FStarC_List.map
            (fun uu___1 ->
               match uu___1 with
               | (b, c) ->
                   (match c with
                    | Mono -> (b, c)
                    | Dropped -> (b, c)
                    | Poly ->
                        let uu___2 =
                          FStarC_List.existsb
                            (fun v ->
                               FStarC_Syntax_Syntax.bv_eq v
                                 b.FStarC_Syntax_Syntax.binder_bv) needed in
                        if uu___2
                        then
                          (FStarC_Effect.op_Colon_Equals changed true;
                           (b, Mono))
                        else (b, Poly))) bcs1 in
        let uu___1 = FStarC_Effect.op_Bang changed in (uu___1, bcs2) in
      let rec fixpoint n bcs1 =
        if n <= Prims.int_zero
        then bcs1
        else
          (let uu___1 = pass bcs1 in
           match uu___1 with
           | (changed, bcs2) ->
               if changed then fixpoint (n - Prims.int_one) bcs2 else bcs2) in
      let bcs1 = fixpoint (FStarC_List.length bs1) bcs in
      let cs1 =
        FStarC_List.map
          (fun uu___1 ->
             match uu___1 with
             | (b, c) ->
                 (match c with
                  | Poly ->
                      let uu___2 = is_type_binder env b in
                      if uu___2 then Dropped else Poly
                  | c1 -> c1)) bcs1 in
      let flags =
        let uu___1 = FStarC_List.map uu___is_Dropped cs1 in
        keep_thunk env bs1 comp uu___1 in
      FStarC_List.map
        (fun uu___1 ->
           match uu___1 with
           | (c, dropped) ->
               (match c with
                | Dropped -> if dropped then Dropped else Poly
                | c1 -> c1)) (FStarC_List.zip cs1 flags)
let classify (env : FStarC_TypeChecker_Env.env)
  (attrs : FStarC_Syntax_Syntax.attribute Prims.list)
  (t : FStarC_Syntax_Syntax.typ) : bclass Prims.list=
  classify_demand env attrs t FStar_Pervasives_Native.None []
let rec observable (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress t in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = b; FStarC_Syntax_Syntax.phi = uu___1;_} ->
      observable b.FStarC_Syntax_Syntax.sort
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = tm; FStarC_Syntax_Syntax.asc = uu___1;
        FStarC_Syntax_Syntax.eff_opt = uu___2;_}
      -> observable tm
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.b1 = b; FStarC_Syntax_Syntax.comp = comp;_} ->
      let b1 =
        let uu___1 =
          let uu___2 = b.FStarC_Syntax_Syntax.binder_bv in
          let uu___3 =
            observable
              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname =
              (uu___2.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (uu___2.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___3
          } in
        {
          FStarC_Syntax_Syntax.binder_bv = uu___1;
          FStarC_Syntax_Syntax.binder_qual =
            (b.FStarC_Syntax_Syntax.binder_qual);
          FStarC_Syntax_Syntax.binder_positivity =
            (b.FStarC_Syntax_Syntax.binder_positivity);
          FStarC_Syntax_Syntax.binder_attrs =
            (b.FStarC_Syntax_Syntax.binder_attrs)
        } in
      let uu___1 =
        let uu___2 = observable (FStarC_Syntax_Util.comp_result comp) in
        FStarC_Syntax_Syntax.mk_Total uu___2 in
      FStarC_Syntax_Util.arrow [b1] uu___1
  | uu___1 -> t
let dead_binders (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) (d : FStarC_Syntax_Syntax.term) :
  Prims.int Prims.list=
  let uu___ = arrow_formals_unfold env t in
  match uu___ with
  | (bs_t, comp) ->
      let uu___1 = FStarC_Syntax_Util.abs_formals d in
      (match uu___1 with
       | (bs_d, body, uu___2) ->
           let live_in_body = FStarC_Syntax_Free.names body in
           let n = FStarC_List.length bs_t in
           let rec tail i bs =
             if i <= Prims.int_zero
             then bs
             else
               (match bs with
                | [] -> []
                | uu___3::bs1 -> tail (i - Prims.int_one) bs1) in
           let res_names =
             let uu___3 =
               let uu___4 = observable (FStarC_Syntax_Util.comp_result comp) in
               FStarC_Syntax_Free.names uu___4 in
             FStarC_Class_Setlike.elems
               (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv)
               uu___3 in
           let rec go i =
             if i >= (n - Prims.int_one)
             then []
             else
               (let bt = FStarC_List.nth bs_t i in
                let later =
                  FStarC_List.collect
                    (fun b ->
                       let uu___3 =
                         let uu___4 =
                           observable
                             (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                         FStarC_Syntax_Free.names uu___4 in
                       FStarC_Class_Setlike.elems
                         (FStarC_FlatSet.setlike_flat_set
                            FStarC_Syntax_Syntax.ord_bv) uu___3)
                    (tail (i + Prims.int_one) bs_t) in
                let in_type =
                  FStarC_List.existsb
                    (fun v ->
                       FStarC_Syntax_Syntax.bv_eq v
                         bt.FStarC_Syntax_Syntax.binder_bv)
                    (FStarC_List.op_At later res_names) in
                let in_body =
                  if (FStarC_List.length bs_d) <= i
                  then true
                  else
                    FStarC_Class_Setlike.mem
                      (FStarC_FlatSet.setlike_flat_set
                         FStarC_Syntax_Syntax.ord_bv)
                      (FStarC_List.nth bs_d i).FStarC_Syntax_Syntax.binder_bv
                      live_in_body in
                let uu___3 = go (i + Prims.int_one) in
                FStarC_List.op_At (if in_type || in_body then [] else [i])
                  uu___3) in
           go Prims.int_zero)
let classify_def (env : FStarC_TypeChecker_Env.env)
  (attrs : FStarC_Syntax_Syntax.attribute Prims.list)
  (t : FStarC_Syntax_Syntax.typ)
  (def : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (demanded : Prims.int Prims.list) : bclass Prims.list=
  let cs = classify_demand env attrs t def demanded in
  let cs1 =
    match def with
    | FStar_Pervasives_Native.None -> cs
    | FStar_Pervasives_Native.Some d ->
        let dead = dead_binders env t d in
        FStarC_List.mapi
          (fun i c ->
             if (c = Mono) && (FStarC_List.mem i dead) then Dropped else c)
          cs in
  match def with
  | FStar_Pervasives_Native.None -> cs1
  | FStar_Pervasives_Native.Some d ->
      let uu___ = FStarC_Syntax_Util.abs_formals d in
      (match uu___ with
       | (bs, uu___1, uu___2) ->
           let rec extra n bs1 =
             match bs1 with
             | [] -> []
             | b::bs2 ->
                 if n > Prims.int_zero
                 then extra (n - Prims.int_one) bs2
                 else
                   (let uu___3 =
                      let uu___4 = is_erased_binder env b in
                      if uu___4 then Dropped else Poly in
                    let uu___4 = extra Prims.int_zero bs2 in uu___3 :: uu___4) in
           let uu___3 = extra (FStarC_List.length cs1) bs in
           FStarC_List.op_At cs1 uu___3)
let has_mono (cs : bclass Prims.list) : Prims.bool=
  FStarC_List.existsb uu___is_Mono cs
let has_dropped (cs : bclass Prims.list) : Prims.bool=
  FStarC_List.existsb uu___is_Dropped cs
