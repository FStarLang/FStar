open Fstarcompiler
open Prims
let op_At (uu___ : unit) :
  'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list=
  FStar_List_Tot_Base.op_At
let name_of_bv (bv : FStarC_Reflection_Types.bv) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_Unseal.unseal
    (FStarC_Reflection_V1_Builtins.inspect_bv bv).FStarC_Reflection_V1_Data.bv_ppname
let bv_to_string (bv : FStarC_Reflection_Types.bv) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr= name_of_bv bv
let name_of_binder (b : FStarC_Reflection_Types.binder) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  name_of_bv (FStar_Reflection_V1_Derived.bv_of_binder b)
let binder_to_string (b : FStarC_Reflection_Types.binder) :
  (Prims.string, unit) FStar_Tactics_Effect.tac_repr=
  bv_to_string (FStar_Reflection_V1_Derived.bv_of_binder b)
exception Goal_not_trivial 
let uu___is_Goal_not_trivial (projectee : Prims.exn) : Prims.bool=
  match projectee with | Goal_not_trivial -> true | uu___ -> false
let goals (uu___ : unit) :
  (FStarC_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.get () ps in
    FStarC_Tactics_Types.goals_of x
let smt_goals (uu___ : unit) :
  (FStarC_Tactics_Types.goal Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.get () ps in
    FStarC_Tactics_Types.smt_goals_of x
let fail (m : Prims.string) : ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    Obj.magic
      (FStarC_Tactics_V1_Builtins.raise_core
         (FStarC_Tactics_Common.TacticFailure
            ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps)
let fail_silently (m : Prims.string) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.set_urgency Prims.int_zero ps;
    Obj.magic
      (FStarC_Tactics_V1_Builtins.raise_core
         (FStarC_Tactics_Common.TacticFailure
            ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None)) ps)
let _cur_goal (uu___ : unit) :
  (FStarC_Tactics_Types.goal, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with | [] -> fail "no more goals" ps | g::uu___1 -> g
let cur_env (uu___ : unit) :
  (FStarC_Reflection_Types.env, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = _cur_goal () ps in FStarC_Tactics_Types.goal_env x
let cur_goal (uu___ : unit) :
  (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = _cur_goal () ps in FStarC_Tactics_Types.goal_type x
let cur_witness (uu___ : unit) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = _cur_goal () ps in FStarC_Tactics_Types.goal_witness x
let cur_binders (uu___ : unit) :
  (FStarC_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_env () ps in FStarC_Reflection_V1_Builtins.binders_of_env x
let with_policy (pol : FStarC_Tactics_Types.guard_policy)
  (f : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.get_guard_policy () ps in
    FStarC_Tactics_V1_Builtins.set_guard_policy pol ps;
    (let x2 = f () ps in FStarC_Tactics_V1_Builtins.set_guard_policy x ps; x2)
let exact (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  with_policy FStarC_Tactics_Types.SMT
    (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true false t)
let exact_with_ref (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  with_policy FStarC_Tactics_Types.SMT
    (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true true t)
let trivial (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.norm
      [Fstarcompiler.FStarC_NormSteps.iota;
      Fstarcompiler.FStarC_NormSteps.zeta;
      Fstarcompiler.FStarC_NormSteps.reify_;
      Fstarcompiler.FStarC_NormSteps.delta;
      Fstarcompiler.FStarC_NormSteps.primops;
      Fstarcompiler.FStarC_NormSteps.simplify;
      Fstarcompiler.FStarC_NormSteps.unmeta] ps;
    (let x1 = cur_goal () ps in
     let x2 = FStar_Reflection_V1_Formula.term_as_formula x1 ps in
     match x2 with
     | FStar_Reflection_V1_Formula.True_ ->
         exact
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_Const
                 FStarC_Reflection_V2_Data.C_Unit)) ps
     | uu___1 -> FStarC_Tactics_V1_Builtins.raise_core Goal_not_trivial ps)
let dismiss (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | [] -> fail "dismiss: no more goals" ps
    | uu___1::gs -> FStarC_Tactics_V1_Builtins.set_goals gs ps
let flip (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    let x1 = goals () ps in
    match x1 with
    | [] -> fail "flip: less than two goals" ps
    | uu___1::[] -> fail "flip: less than two goals" ps
    | g1::g2::gs -> FStarC_Tactics_V1_Builtins.set_goals (g2 :: g1 :: gs) ps
let qed (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with | [] -> () | uu___1 -> fail "qed: not done!" ps
let debug (m : Prims.string) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.debugging () ps in
    if x then FStarC_Tactics_V1_Builtins.print m ps else ()
let smt (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = goals () ps in let x2 = smt_goals () ps in (x1, x2) in
    match x with
    | ([], uu___1) -> fail "smt: no active goals" ps
    | (g::gs, gs') ->
        (FStarC_Tactics_V1_Builtins.set_goals gs ps;
         FStarC_Tactics_V1_Builtins.set_smt_goals (g :: gs') ps)
let idtac (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun uu___ -> Obj.magic (fun uu___1 -> ())) uu___
let later (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | g::gs -> FStarC_Tactics_V1_Builtins.set_goals ((op_At ()) gs [g]) ps
    | uu___1 -> fail "later: no goals" ps
let apply (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply true false false t
let apply_noinst (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply true true false t
let apply_lemma (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply_lemma false false t
let trefl (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_trefl false
let trefl_guard (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_trefl true
let commute_applied_match (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_commute_applied_match ()
let apply_lemma_noinst (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply_lemma true false t
let apply_lemma_rw (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply_lemma false true t
let apply_raw (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.t_apply false false false t
let exact_guard (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  with_policy FStarC_Tactics_Types.Goal
    (fun uu___ -> FStarC_Tactics_V1_Builtins.t_exact true false t)
let t_pointwise (d : FStarC_Tactics_Types.direction)
  (tau : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x uu___ =
      (fun t ->
         Obj.magic (fun uu___ -> (true, FStarC_Tactics_Types.Continue)))
        uu___ in
    let x1 uu___ = tau () in
    FStarC_Tactics_V1_Builtins.ctrl_rewrite d x x1 ps
let topdown_rewrite
  (ctrl :
    FStarC_Reflection_Types.term ->
      ((Prims.bool * Prims.int), unit) FStar_Tactics_Effect.tac_repr)
  (rw : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x t ps1 =
      let x1 = ctrl t ps1 in
      match x1 with
      | (b, i) ->
          let x2 =
            match i with
            | uu___ when uu___ = Prims.int_zero ->
                FStarC_Tactics_Types.Continue
            | uu___ when uu___ = Prims.int_one -> FStarC_Tactics_Types.Skip
            | uu___ when uu___ = (Prims.of_int (2)) ->
                FStarC_Tactics_Types.Abort
            | uu___ -> fail "topdown_rewrite: bad value from ctrl" ps1 in
          (b, x2) in
    FStarC_Tactics_V1_Builtins.ctrl_rewrite FStarC_Tactics_Types.TopDown x rw
      ps
let pointwise (tau : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  t_pointwise FStarC_Tactics_Types.BottomUp tau
let pointwise' (tau : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  t_pointwise FStarC_Tactics_Types.TopDown tau
let cur_module (uu___ : unit) :
  (FStarC_Reflection_Types.name, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.top_env () ps in
    FStarC_Reflection_V1_Builtins.moduleof x
let open_modules (uu___ : unit) :
  (FStarC_Reflection_Types.name Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.top_env () ps in
    FStarC_Reflection_V1_Builtins.env_open_modules x
let fresh_uvar
  (o : FStarC_Reflection_Types.typ FStar_Pervasives_Native.option) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_env () ps in FStarC_Tactics_V1_Builtins.uvar_env x o ps
let unify (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_env () ps in FStarC_Tactics_V1_Builtins.unify_env x t1 t2 ps
let unify_guard (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_env () ps in
    FStarC_Tactics_V1_Builtins.unify_guard_env x t1 t2 ps
let tmatch (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_env () ps in FStarC_Tactics_V1_Builtins.match_env x t1 t2 ps
let divide (n : Prims.int)
  (l : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (r : unit -> ('b, unit) FStar_Tactics_Effect.tac_repr) :
  (('a * 'b), unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    if n < Prims.int_zero then fail "divide: negative n" ps else ();
    (let x1 = let x2 = goals () ps in let x3 = smt_goals () ps in (x2, x3) in
     match x1 with
     | (gs, sgs) ->
         let x2 = FStar_List_Tot_Base.splitAt n gs in
         (match x2 with
          | (gs1, gs2) ->
              (FStarC_Tactics_V1_Builtins.set_goals gs1 ps;
               FStarC_Tactics_V1_Builtins.set_smt_goals [] ps;
               (let x5 = l () ps in
                let x6 =
                  let x7 = goals () ps in
                  let x8 = smt_goals () ps in (x7, x8) in
                match x6 with
                | (gsl, sgsl) ->
                    (FStarC_Tactics_V1_Builtins.set_goals gs2 ps;
                     FStarC_Tactics_V1_Builtins.set_smt_goals [] ps;
                     (let x9 = r () ps in
                      let x10 =
                        let x11 = goals () ps in
                        let x12 = smt_goals () ps in (x11, x12) in
                      match x10 with
                      | (gsr, sgsr) ->
                          (FStarC_Tactics_V1_Builtins.set_goals
                             ((op_At ()) gsl gsr) ps;
                           FStarC_Tactics_V1_Builtins.set_smt_goals
                             ((op_At ()) sgs ((op_At ()) sgsl sgsr)) ps;
                           (x5, x9))))))))
let rec iseq
  (uu___ : (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) Prims.list) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun ts ->
     match ts with
     | t::ts1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (divide Prims.int_one t (fun uu___ -> iseq ts1)))
                 (fun uu___ uu___1 -> ())))
     | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))) uu___
let focus (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | [] -> fail "focus: no goals" ps
    | g::gs ->
        let x1 = smt_goals () ps in
        (FStarC_Tactics_V1_Builtins.set_goals [g] ps;
         FStarC_Tactics_V1_Builtins.set_smt_goals [] ps;
         (let x4 = t () ps in
          (let x6 = let x7 = goals () ps in (op_At ()) x7 gs in
           FStarC_Tactics_V1_Builtins.set_goals x6 ps);
          (let x7 = let x8 = smt_goals () ps in (op_At ()) x8 x1 in
           FStarC_Tactics_V1_Builtins.set_smt_goals x7 ps);
          x4))
let dump1 (m : Prims.string) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  focus (fun uu___ -> FStarC_Tactics_V1_Builtins.dump m)
let rec mapAll :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ps ->
    let x = goals () ps in
    match x with
    | [] -> []
    | uu___::uu___1 ->
        let x1 = divide Prims.int_one t (fun uu___2 -> mapAll t) ps in
        (match x1 with | (h, t1) -> h :: t1)
let rec iterAll (t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | [] -> ()
    | uu___::uu___1 ->
        let x1 = divide Prims.int_one t (fun uu___2 -> iterAll t) ps in ()
let iterAllSMT (t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = goals () ps in let x2 = smt_goals () ps in (x1, x2) in
    match x with
    | (gs, sgs) ->
        (FStarC_Tactics_V1_Builtins.set_goals sgs ps;
         FStarC_Tactics_V1_Builtins.set_smt_goals [] ps;
         iterAll t ps;
         (let x4 =
            let x5 = goals () ps in let x6 = smt_goals () ps in (x5, x6) in
          match x4 with
          | (gs', sgs') ->
              (FStarC_Tactics_V1_Builtins.set_goals gs ps;
               FStarC_Tactics_V1_Builtins.set_smt_goals ((op_At ()) gs' sgs')
                 ps)))
let seq (f : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  (g : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  focus (fun uu___ ps -> f () ps; iterAll g ps)
let exact_args (qs : FStarC_Reflection_V1_Data.aqualv Prims.list)
  (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  focus
    (fun uu___ ps ->
       let x = FStar_List_Tot_Base.length qs in
       let x1 =
         FStar_Tactics_Util.repeatn x
           (fun uu___1 -> fresh_uvar FStar_Pervasives_Native.None) ps in
       let x2 =
         let x3 = FStar_Tactics_Util.zip x1 qs ps in
         FStar_Reflection_V1_Derived.mk_app t x3 in
       exact x2 ps;
       FStar_Tactics_Util.iter
         (fun uu___1 ->
            (fun uv ->
               if FStar_Reflection_V1_Derived.is_uvar uv
               then
                 Obj.magic
                   (Obj.repr (FStarC_Tactics_V1_Builtins.unshelve uv))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
              uu___1) (FStar_List_Tot_Base.rev x1) ps)
let exact_n (n : Prims.int) (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_Util.repeatn n
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic (fun uu___1 -> FStarC_Reflection_V1_Data.Q_Explicit))
             uu___) ps in
    exact_args x t ps
let ngoals (uu___ : unit) : (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = goals () ps in FStar_List_Tot_Base.length x
let ngoals_smt (uu___ : unit) :
  (Prims.int, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = smt_goals () ps in FStar_List_Tot_Base.length x
let fresh_bv (uu___ : unit) :
  (FStarC_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.fresh () ps in
    FStarC_Tactics_V1_Builtins.fresh_bv_named
      (Prims.strcat "x" (Prims.string_of_int x)) ps
let fresh_binder_named (nm : Prims.string) (t : FStarC_Reflection_Types.typ)
  : (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.fresh_bv_named nm ps in
    FStar_Reflection_V1_Derived.mk_binder x t
let fresh_binder (t : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.fresh () ps in
    fresh_binder_named (Prims.strcat "x" (Prims.string_of_int x)) t ps
let fresh_implicit_binder_named (nm : Prims.string)
  (t : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.fresh_bv_named nm ps in
    FStar_Reflection_V1_Derived.mk_implicit_binder x t
let fresh_implicit_binder (t : FStarC_Reflection_Types.typ) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.fresh () ps in
    fresh_implicit_binder_named (Prims.strcat "x" (Prims.string_of_int x)) t
      ps
let guard (uu___ : Prims.bool) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun b ->
     if Prims.op_Negation b
     then Obj.magic (Obj.repr (fail "guard failed"))
     else
       Obj.magic
         (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
    uu___
let try_with (f : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (h : Prims.exn -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.catch f ps in
    match x with
    | Fstarcompiler.FStar_Pervasives.Inl e -> h e ps
    | Fstarcompiler.FStar_Pervasives.Inr x1 -> x1
let trytac (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a FStar_Pervasives_Native.option, unit) FStar_Tactics_Effect.tac_repr=
  try_with
    (fun uu___ ->
       match () with
       | () -> (fun ps -> let x = t () ps in FStar_Pervasives_Native.Some x))
    (fun uu___ ->
       (fun uu___ -> Obj.magic (fun uu___1 -> FStar_Pervasives_Native.None))
         uu___)
let or_else (t1 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (t2 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  try_with (fun uu___ -> match () with | () -> t1 ()) (fun uu___ -> t2 ())
let op_Less_Bar_Greater
  (t1 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (t2 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) (uu___ : unit) :
  ('a, unit) FStar_Tactics_Effect.tac_repr= or_else t1 t2
let first
  (ts : (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) Prims.list) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  FStar_List_Tot_Base.fold_right op_Less_Bar_Greater ts
    (fun uu___ -> fail "no tactics to try") ()
let rec repeat :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ps ->
    let x = FStarC_Tactics_V1_Builtins.catch t ps in
    match x with
    | Fstarcompiler.FStar_Pervasives.Inl uu___ -> []
    | Fstarcompiler.FStar_Pervasives.Inr x1 ->
        let x2 = repeat t ps in x1 :: x2
let repeat1 (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = t () ps in let x1 = repeat t ps in x :: x1
let repeat' (f : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = repeat f ps in ()
let norm_term (s : Fstarcompiler.FStarC_NormSteps.norm_step Prims.list)
  (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      try_with (fun uu___ -> match () with | () -> cur_env ())
        (fun uu___ -> FStarC_Tactics_V1_Builtins.top_env ()) ps in
    FStarC_Tactics_V1_Builtins.norm_term_env x s t ps
let join_all_smt_goals (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = goals () ps in let x2 = smt_goals () ps in (x1, x2) in
    match x with
    | (gs, sgs) ->
        (FStarC_Tactics_V1_Builtins.set_smt_goals [] ps;
         FStarC_Tactics_V1_Builtins.set_goals sgs ps;
         repeat' FStarC_Tactics_V1_Builtins.join ps;
         (let x4 = goals () ps in
          FStarC_Tactics_V1_Builtins.set_goals gs ps;
          FStarC_Tactics_V1_Builtins.set_smt_goals x4 ps))
let discard (tau : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = tau () ps in ()
let rec repeatseq :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ps ->
    let x =
      trytac
        (fun uu___ -> seq (discard t) (discard (fun uu___1 -> repeatseq t)))
        ps in
    ()
let tadmit (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.tadmit_t
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit))
let admit1 (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  tadmit ()
let admit_all (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = repeat tadmit ps in ()
let is_guard (uu___ : unit) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = _cur_goal () ps in FStarC_Tactics_Types.is_guard x
let skip_guard (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = is_guard () ps in if x then smt () ps else fail "" ps
let guards_to_smt (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = repeat skip_guard ps in ()
let simpl (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.norm
    [Fstarcompiler.FStarC_NormSteps.simplify;
    Fstarcompiler.FStarC_NormSteps.primops]
let whnf (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.norm
    [Fstarcompiler.FStarC_NormSteps.weak;
    Fstarcompiler.FStarC_NormSteps.hnf;
    Fstarcompiler.FStarC_NormSteps.primops;
    Fstarcompiler.FStarC_NormSteps.delta]
let compute (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.norm
    [Fstarcompiler.FStarC_NormSteps.primops;
    Fstarcompiler.FStarC_NormSteps.iota;
    Fstarcompiler.FStarC_NormSteps.delta;
    Fstarcompiler.FStarC_NormSteps.zeta]
let intros (uu___ : unit) :
  (FStarC_Reflection_Types.binder Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  repeat FStarC_Tactics_V1_Builtins.intro
let intros' (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = intros () ps in ()
let destruct (tm : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = FStarC_Tactics_V1_Builtins.t_destruct tm ps in ()
let destruct_intros (tm : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  seq
    (fun uu___ ps ->
       let x = FStarC_Tactics_V1_Builtins.t_destruct tm ps in ()) intros'
let __cut (f : 'a -> 'b) (x : 'a) : 'b= f x
let tcut (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_goal () ps in
    let x1 =
      FStar_Reflection_V1_Derived.mk_e_app
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "V1"; "Derived"; "__cut"]))) [t; x] in
    apply x1 ps; FStarC_Tactics_V1_Builtins.intro () ps
let pose (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V1"; "Derived"; "__cut"]))) ps;
    flip () ps;
    exact t ps;
    FStarC_Tactics_V1_Builtins.intro () ps
let intro_as (s : Prims.string) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.intro () ps in
    FStarC_Tactics_V1_Builtins.rename_to x s ps
let pose_as (s : Prims.string) (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = pose t ps in FStarC_Tactics_V1_Builtins.rename_to x s ps
let for_each_binder
  (f :
    FStarC_Reflection_Types.binder ->
      ('a, unit) FStar_Tactics_Effect.tac_repr)
  : ('a Prims.list, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = cur_binders () ps in FStar_Tactics_Util.map f x ps
let rec revert_all (uu___ : FStarC_Reflection_Types.binders) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
     | uu___::tl ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStarC_Tactics_V1_Builtins.revert ()))
                 (fun uu___1 ->
                    (fun uu___1 -> Obj.magic (revert_all tl)) uu___1))))
    uu___
let bv_to_term (bv : FStarC_Reflection_Types.bv) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.pack (FStarC_Reflection_V1_Data.Tv_Var bv)
let binder_to_term (b : FStarC_Reflection_Types.binder) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Reflection_V1_Builtins.inspect_binder b in
    bv_to_term x.FStarC_Reflection_V1_Data.binder_bv ps
let binder_sort (uu___ : FStarC_Reflection_Types.binder) :
  (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr=
  (fun b ->
     Obj.magic
       (fun uu___ ->
          (FStarC_Reflection_V1_Builtins.inspect_binder b).FStarC_Reflection_V1_Data.binder_sort))
    uu___
let rec __assumption_aux (bs : FStarC_Reflection_Types.binders) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  match bs with
  | [] -> fail "no assumption matches goal"
  | b::bs1 ->
      FStar_Tactics_Effect.tac_bind (Obj.magic (binder_to_term b))
        (fun uu___ ->
           (fun t ->
              Obj.magic
                (try_with (fun uu___ -> match () with | () -> exact t)
                   (fun uu___ ->
                      try_with
                        (fun uu___1 ->
                           match () with
                           | () ->
                               (fun ps ->
                                  apply
                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_FVar
                                          (FStarC_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Squash";
                                             "return_squash"]))) ps;
                                  exact t ps))
                        (fun uu___1 -> __assumption_aux bs1)))) uu___)
let assumption (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = cur_binders () ps in __assumption_aux x ps
let destruct_equality_implication (t : FStarC_Reflection_Types.term) :
  ((FStar_Reflection_V1_Formula.formula * FStarC_Reflection_Types.term)
     FStar_Pervasives_Native.option,
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Reflection_V1_Formula.term_as_formula t ps in
    match x with
    | FStar_Reflection_V1_Formula.Implies (lhs, rhs) ->
        let x1 = FStar_Reflection_V1_Formula.term_as_formula' lhs ps in
        (match x1 with
         | FStar_Reflection_V1_Formula.Comp
             (FStar_Reflection_V1_Formula.Eq uu___, uu___1, uu___2) ->
             FStar_Pervasives_Native.Some (x1, rhs)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let rewrite' (b : FStarC_Reflection_Types.binder) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  op_Less_Bar_Greater
    (op_Less_Bar_Greater (fun uu___ -> FStarC_Tactics_V1_Builtins.rewrite b)
       (fun uu___ ps ->
          FStarC_Tactics_V1_Builtins.binder_retype b ps;
          apply_lemma
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_FVar
                  (FStarC_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V1"; "Derived"; "__eq_sym"]))) ps;
          FStarC_Tactics_V1_Builtins.rewrite b ps))
    (fun uu___ -> fail "rewrite' failed") ()
let rec try_rewrite_equality (uu___1 : FStarC_Reflection_Types.term)
  (uu___ : FStarC_Reflection_Types.binders) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun x bs ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
     | x_t::bs1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (FStar_Reflection_V1_Formula.term_as_formula
                       (FStar_Reflection_V1_Derived.type_of_binder x_t)))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStar_Reflection_V1_Formula.Comp
                           (FStar_Reflection_V1_Formula.Eq uu___1, y, uu___2)
                           ->
                           if FStar_Reflection_TermEq_Simple.term_eq x y
                           then
                             Obj.magic
                               (FStarC_Tactics_V1_Builtins.rewrite x_t)
                           else Obj.magic (try_rewrite_equality x bs1)
                       | uu___1 -> Obj.magic (try_rewrite_equality x bs1))
                      uu___)))) uu___1 uu___
let rec rewrite_all_context_equalities
  (uu___ : FStarC_Reflection_Types.binders) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
     | x_t::bs1 ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind
                 (Obj.magic
                    (try_with
                       (fun uu___ ->
                          match () with
                          | () -> FStarC_Tactics_V1_Builtins.rewrite x_t)
                       (fun uu___ ->
                          (fun uu___ -> Obj.magic (fun uu___1 -> ())) uu___)))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic (rewrite_all_context_equalities bs1)) uu___))))
    uu___
let rewrite_eqs_from_context (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = cur_binders () ps in rewrite_all_context_equalities x ps
let rewrite_equality (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps -> let x = cur_binders () ps in try_rewrite_equality t x ps
let unfold_def (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V1_Builtins.inspect t ps in
    match x with
    | FStarC_Reflection_V1_Data.Tv_FVar fv ->
        let x1 =
          FStarC_Reflection_V1_Builtins.implode_qn
            (FStarC_Reflection_V1_Builtins.inspect_fv fv) in
        FStarC_Tactics_V1_Builtins.norm
          [Fstarcompiler.FStarC_NormSteps.delta_fully [x1]] ps
    | uu___ -> fail "unfold_def: term is not a fv" ps
let l_to_r (lems : FStarC_Reflection_Types.term Prims.list) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x uu___ ps1 =
      let x1 =
        FStar_Tactics_Util.fold_left
          (fun uu___2 uu___1 ->
             (fun k l ->
                Obj.magic
                  (fun uu___1 uu___2 ->
                     or_else (fun uu___3 -> apply_lemma_rw l) k)) uu___2
               uu___1) trefl lems ps1 in
      x1 () ps1 in
    pointwise x ps
let mk_squash (t : FStarC_Reflection_Types.term) :
  FStarC_Reflection_Types.term=
  let sq =
    FStarC_Reflection_V1_Builtins.pack_ln
      (FStarC_Reflection_V1_Data.Tv_FVar
         (FStarC_Reflection_V1_Builtins.pack_fv
            FStar_Reflection_Const.squash_qn)) in
  FStar_Reflection_V1_Derived.mk_e_app sq [t]
let mk_sq_eq (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) : FStarC_Reflection_Types.term=
  let eq =
    FStarC_Reflection_V1_Builtins.pack_ln
      (FStarC_Reflection_V1_Data.Tv_FVar
         (FStarC_Reflection_V1_Builtins.pack_fv FStar_Reflection_Const.eq2_qn)) in
  mk_squash (FStar_Reflection_V1_Derived.mk_e_app eq [t1; t2])
let grewrite (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = tcut (mk_sq_eq t1 t2) ps in
    let x1 =
      FStarC_Reflection_V1_Builtins.pack_ln
        (FStarC_Reflection_V1_Data.Tv_Var
           (FStar_Reflection_V1_Derived.bv_of_binder x)) in
    pointwise
      (fun uu___ ps1 ->
         let x2 =
           let x3 =
             let x4 = cur_goal () ps1 in
             FStar_Reflection_V1_Formula.term_as_formula x4 ps1 in
           match x3 with
           | FStar_Reflection_V1_Formula.Comp
               (FStar_Reflection_V1_Formula.Eq uu___1, lhs, rhs) ->
               (match FStarC_Reflection_V1_Builtins.inspect_ln lhs with
                | FStarC_Reflection_V1_Data.Tv_Uvar (uu___2, uu___3) -> true
                | uu___2 -> false)
           | uu___1 -> false in
         if x2
         then trefl () ps1
         else
           try_with (fun uu___2 -> match () with | () -> exact x1)
             (fun uu___2 -> trefl ()) ps1) ps
let grewrite_eq (b : FStarC_Reflection_Types.binder) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Reflection_V1_Formula.term_as_formula
        (FStar_Reflection_V1_Derived.type_of_binder b) ps in
    match x with
    | FStar_Reflection_V1_Formula.Comp
        (FStar_Reflection_V1_Formula.Eq uu___, l, r) ->
        (grewrite l r ps;
         iseq
           [idtac;
           (fun uu___1 ps1 -> let x2 = binder_to_term b ps1 in exact x2 ps1)]
           ps)
    | uu___ ->
        let x1 =
          FStar_Reflection_V1_Formula.term_as_formula'
            (FStar_Reflection_V1_Derived.type_of_binder b) ps in
        (match x1 with
         | FStar_Reflection_V1_Formula.Comp
             (FStar_Reflection_V1_Formula.Eq uu___1, l, r) ->
             (grewrite l r ps;
              iseq
                [idtac;
                (fun uu___2 ps1 ->
                   apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "V1";
                              "Derived";
                              "__un_sq_eq"]))) ps1;
                   (let x4 = binder_to_term b ps1 in exact x4 ps1))] ps)
         | uu___1 -> fail "grewrite_eq: binder type is not an equality" ps)
let rec apply_squash_or_lem (d : Prims.nat)
  (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  try_with (fun uu___ -> match () with | () -> apply t)
    (fun uu___ ->
       try_with
         (fun uu___1 ->
            match () with
            | () ->
                (fun ps ->
                   apply
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Squash"; "return_squash"]))) ps;
                   apply t ps))
         (fun uu___1 ->
            try_with (fun uu___2 -> match () with | () -> apply_lemma t)
              (fun uu___2 ->
                 if d <= Prims.int_zero
                 then fail "mapply: out of fuel"
                 else
                   FStar_Tactics_Effect.tac_bind
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (Obj.magic (cur_env ()))
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 Obj.magic
                                   (FStarC_Tactics_V1_Builtins.tc uu___4 t))
                                uu___4)))
                     (fun uu___4 ->
                        (fun ty ->
                           Obj.magic
                             (fun ps ->
                                let x =
                                  FStar_Tactics_V1_SyntaxHelpers.collect_arr
                                    ty ps in
                                match x with
                                | (tys, c) ->
                                    (match FStarC_Reflection_V1_Builtins.inspect_comp
                                             c
                                     with
                                     | FStarC_Reflection_V1_Data.C_Lemma
                                         (pre, post, uu___4) ->
                                         let x1 =
                                           FStarC_Reflection_V2_Builtins.pack_ln
                                             (FStarC_Reflection_V2_Data.Tv_App
                                                (post,
                                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                                      (FStarC_Reflection_V2_Data.Tv_Const
                                                         FStarC_Reflection_V2_Data.C_Unit)),
                                                    FStarC_Reflection_V2_Data.Q_Explicit))) in
                                         let x2 = norm_term [] x1 ps in
                                         let x3 =
                                           FStar_Reflection_V1_Formula.term_as_formula'
                                             x2 ps in
                                         (match x3 with
                                          | FStar_Reflection_V1_Formula.Implies
                                              (p, q) ->
                                              (apply_lemma
                                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                       (FStarC_Reflection_V2_Builtins.pack_fv
                                                          ["FStar";
                                                          "Tactics";
                                                          "V1";
                                                          "Derived";
                                                          "push1"]))) ps;
                                               apply_squash_or_lem
                                                 (d - Prims.int_one) t ps)
                                          | uu___5 ->
                                              fail "mapply: can't apply (1)"
                                                ps)
                                     | FStarC_Reflection_V1_Data.C_Total rt
                                         ->
                                         (match FStar_Reflection_V1_Derived.unsquash_term
                                                  rt
                                          with
                                          | FStar_Pervasives_Native.Some rt1
                                              ->
                                              let x1 = norm_term [] rt1 ps in
                                              let x2 =
                                                FStar_Reflection_V1_Formula.term_as_formula'
                                                  x1 ps in
                                              (match x2 with
                                               | FStar_Reflection_V1_Formula.Implies
                                                   (p, q) ->
                                                   (apply_lemma
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "V1";
                                                               "Derived";
                                                               "push1"]))) ps;
                                                    apply_squash_or_lem
                                                      (d - Prims.int_one) t
                                                      ps)
                                               | uu___4 ->
                                                   fail
                                                     "mapply: can't apply (1)"
                                                     ps)
                                          | FStar_Pervasives_Native.None ->
                                              let x1 = norm_term [] rt ps in
                                              let x2 =
                                                FStar_Reflection_V1_Formula.term_as_formula'
                                                  x1 ps in
                                              (match x2 with
                                               | FStar_Reflection_V1_Formula.Implies
                                                   (p, q) ->
                                                   (apply_lemma
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Tactics";
                                                               "V1";
                                                               "Derived";
                                                               "push1"]))) ps;
                                                    apply_squash_or_lem
                                                      (d - Prims.int_one) t
                                                      ps)
                                               | uu___4 ->
                                                   (apply
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Squash";
                                                               "return_squash"])))
                                                      ps;
                                                    apply t ps)))
                                     | uu___4 ->
                                         fail "mapply: can't apply (2)" ps)))
                          uu___4))))
let mapply (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  apply_squash_or_lem (Prims.of_int (10)) t
let admit_dump_t (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.dump "Admitting" ps;
    apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "admit"]))) ps
let admit_dump (x : unit -> 'a) (uu___ : unit) : 'a= x ()
let magic_dump_t (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.dump "Admitting" ps;
    apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "magic"]))) ps;
    exact
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit))
      ps
let magic_dump (x : 'a) (uu___ : unit) : 'a= x
let change_with (t1 : FStarC_Reflection_Types.term)
  (t2 : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  focus (fun uu___ ps -> grewrite t1 t2 ps; iseq [idtac; trivial] ps)
let change_sq (t1 : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStarC_Tactics_V1_Builtins.change
    (FStar_Reflection_V1_Derived.mk_e_app
       (FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "squash"])))
       [t1])
let finish_by (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = t () ps in
    or_else qed (fun uu___ -> fail "finish_by: not finished") ps; x
let solve_then (t1 : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr)
  (t2 : 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr) :
  ('b, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.dup () ps;
    (let x1 = focus (fun uu___ -> finish_by t1) ps in
     let x2 = t2 x1 ps in trefl () ps; x2)
let add_elem (t : unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) :
  ('a, unit) FStar_Tactics_Effect.tac_repr=
  focus
    (fun uu___ ps ->
       apply
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Cons"]))) ps;
       focus (fun uu___1 ps1 -> let x1 = t () ps1 in qed () ps1; x1) ps)
let specialize (f : 'a) (l : Prims.string Prims.list) (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  solve_then
    (fun uu___1 ps ->
       let x =
         Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
       exact x ps)
    (fun uu___1 ->
       FStarC_Tactics_V1_Builtins.norm
         [Fstarcompiler.FStarC_NormSteps.delta_only l;
         Fstarcompiler.FStarC_NormSteps.iota;
         Fstarcompiler.FStarC_NormSteps.zeta])
let tlabel (l : Prims.string) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | [] -> fail "tlabel: no goals" ps
    | h::t ->
        FStarC_Tactics_V1_Builtins.set_goals
          ((FStarC_Tactics_Types.set_label l h) :: t) ps
let tlabel' (l : Prims.string) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = goals () ps in
    match x with
    | [] -> fail "tlabel': no goals" ps
    | h::t ->
        let x1 =
          FStarC_Tactics_Types.set_label
            (Prims.strcat l (FStarC_Tactics_Types.get_label h)) h in
        FStarC_Tactics_V1_Builtins.set_goals (x1 :: t) ps
let focus_all (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    (let x1 =
       let x2 = goals () ps in let x3 = smt_goals () ps in (op_At ()) x2 x3 in
     FStarC_Tactics_V1_Builtins.set_goals x1 ps);
    FStarC_Tactics_V1_Builtins.set_smt_goals [] ps
let rec extract_nth :
  'a .
    Prims.nat ->
      'a Prims.list -> ('a * 'a Prims.list) FStar_Pervasives_Native.option
  =
  fun n l ->
    match (n, l) with
    | (uu___, []) -> FStar_Pervasives_Native.None
    | (uu___, hd::tl) when uu___ = Prims.int_zero ->
        FStar_Pervasives_Native.Some (hd, tl)
    | (uu___, hd::tl) ->
        (match extract_nth (n - Prims.int_one) tl with
         | FStar_Pervasives_Native.Some (hd', tl') ->
             FStar_Pervasives_Native.Some (hd', (hd :: tl'))
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let bump_nth (n : Prims.pos) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = let x1 = goals () ps in extract_nth (n - Prims.int_one) x1 in
    match x with
    | FStar_Pervasives_Native.None -> fail "bump_nth: not that many goals" ps
    | FStar_Pervasives_Native.Some (h, t) ->
        FStarC_Tactics_V1_Builtins.set_goals (h :: t) ps
let rec destruct_list (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V1_SyntaxHelpers.collect_app t ps in
    match x with
    | (head, args) ->
        (match ((FStarC_Reflection_V1_Builtins.inspect_ln head), args) with
         | (FStarC_Reflection_V1_Data.Tv_FVar fv,
            (a1, FStarC_Reflection_V1_Data.Q_Explicit)::(a2,
                                                         FStarC_Reflection_V1_Data.Q_Explicit)::[])
             ->
             Obj.magic
               (Obj.repr
                  (if
                     (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                       FStar_Reflection_Const.cons_qn
                   then Obj.repr (let x1 = destruct_list a2 ps in a1 :: x1)
                   else
                     Obj.repr
                       (FStarC_Tactics_V1_Builtins.raise_core
                          FStarC_Tactics_Common.NotAListLiteral ps)))
         | (FStarC_Reflection_V1_Data.Tv_FVar fv,
            (uu___, FStarC_Reflection_V1_Data.Q_Implicit)::(a1,
                                                            FStarC_Reflection_V1_Data.Q_Explicit)::
            (a2, FStarC_Reflection_V1_Data.Q_Explicit)::[]) ->
             Obj.magic
               (Obj.repr
                  (if
                     (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                       FStar_Reflection_Const.cons_qn
                   then Obj.repr (let x1 = destruct_list a2 ps in a1 :: x1)
                   else
                     Obj.repr
                       (FStarC_Tactics_V1_Builtins.raise_core
                          FStarC_Tactics_Common.NotAListLiteral ps)))
         | (FStarC_Reflection_V1_Data.Tv_FVar fv, uu___) ->
             Obj.magic
               (Obj.repr
                  (if
                     (FStarC_Reflection_V1_Builtins.inspect_fv fv) =
                       FStar_Reflection_Const.nil_qn
                   then Obj.repr []
                   else
                     Obj.repr
                       (FStarC_Tactics_V1_Builtins.raise_core
                          FStarC_Tactics_Common.NotAListLiteral ps)))
         | uu___ ->
             Obj.magic
               (Obj.repr
                  (FStarC_Tactics_V1_Builtins.raise_core
                     FStarC_Tactics_Common.NotAListLiteral ps)))
let get_match_body (uu___ : unit) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = cur_goal () ps in FStar_Reflection_V1_Derived.unsquash_term x1 in
    match x with
    | FStar_Pervasives_Native.None -> fail "" ps
    | FStar_Pervasives_Native.Some t ->
        let x1 = FStar_Tactics_V1_SyntaxHelpers.inspect_unascribe t ps in
        (match x1 with
         | FStarC_Reflection_V1_Data.Tv_Match (sc, uu___1, uu___2) -> sc
         | uu___1 -> fail "Goal is not a match" ps)
let rec last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun x ->
       match x with
       | [] -> Obj.magic (Obj.repr (fail "last: empty list"))
       | x1::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x1)))
       | uu___::xs -> Obj.magic (Obj.repr (last xs))) uu___
let branch_on_match (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  focus
    (fun uu___1 ps ->
       let x = get_match_body () ps in
       let x1 = FStarC_Tactics_V1_Builtins.t_destruct x ps in
       iterAll
         (fun uu___2 ps1 ->
            let x2 = repeat FStarC_Tactics_V1_Builtins.intro ps1 in
            let x3 = last x2 ps1 in
            grewrite_eq x3 ps1;
            FStarC_Tactics_V1_Builtins.norm
              [Fstarcompiler.FStarC_NormSteps.iota] ps1) ps)
let nth_binder (i : Prims.int) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_binders () ps in
    let x1 =
      if i >= Prims.int_zero then i else (FStar_List_Tot_Base.length x) + i in
    let x2 = if x1 < Prims.int_zero then fail "not enough binders" ps else x1 in
    match FStar_List_Tot_Base.nth x x2 with
    | FStar_Pervasives_Native.None -> fail "not enough binders" ps
    | FStar_Pervasives_Native.Some b -> b
let rec mk_abs (uu___1 : FStarC_Reflection_Types.binder Prims.list)
  (uu___ : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  (fun args t ->
     match args with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> t))
     | a::args' ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (mk_abs args' t))
                 (fun uu___ ->
                    (fun t' ->
                       Obj.magic
                         (FStarC_Tactics_V1_Builtins.pack
                            (FStarC_Reflection_V1_Data.Tv_Abs (a, t'))))
                      uu___)))) uu___1 uu___
let string_to_term_with_lb
  (letbindings : (Prims.string * FStarC_Reflection_Types.term) Prims.list)
  (e : FStarC_Reflection_Types.env) (t : Prims.string) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStarC_Reflection_V2_Builtins.pack_ln
        FStarC_Reflection_V2_Data.Tv_Unknown in
    let x1 =
      FStar_Tactics_Util.fold_left
        (fun uu___ uu___1 ->
           match (uu___, uu___1) with
           | ((e1, lb_bvs), (i, v)) ->
               FStar_Tactics_Effect.tac_bind
                 (Obj.magic (FStarC_Tactics_V1_Builtins.push_bv_dsenv e1 i))
                 (fun uu___2 uu___3 ->
                    match uu___2 with | (e2, bv) -> (e2, ((v, bv) :: lb_bvs))))
        (e, []) letbindings ps in
    match x1 with
    | (e1, lb_bvs) ->
        let x2 = FStarC_Tactics_V1_Builtins.string_to_term e1 t ps in
        FStar_Tactics_Util.fold_left
          (fun t1 uu___ ->
             match uu___ with
             | (i, bv) ->
                 FStarC_Tactics_V1_Builtins.pack
                   (FStarC_Reflection_V1_Data.Tv_Let
                      (false, [], bv, x, i, t1))) x2 lb_bvs ps
let trans (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  apply_lemma
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Tactics"; "V1"; "Derived"; "lem_trans"])))
