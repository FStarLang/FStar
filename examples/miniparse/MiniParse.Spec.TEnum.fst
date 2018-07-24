module MiniParse.Spec.TEnum
include MiniParse.Spec.Combinators
include MiniParse.Tac.Base
include MiniParse.Spec.Int

module T = FStar.Tactics
module U16 = FStar.UInt16

let rec mk_tenum_branches (ty: T.term) (vty: T.term) (v: nat) (accu: list T.branch) (l: list T.name) : T.Tac (list T.branch) =
  match l with
  | [] -> accu
  | n :: q ->
    let v' = v + 1 in
    let env = T.cur_env () in
    let v = T.mk_app (`(mk_u16)) [pack_nat v, T.Q_Explicit] in
    let v = T.pack (T.Tv_AscribedT v vty None) in
    let pat =
      T.Pat_Cons (T.pack_fv n) []
    in
    let br : T.branch = (pat, v) in
    let accu' = br :: accu in
    begin match q with
    | [] ->
      let b = T.fresh_binder ty in
      let pat = T.Pat_Var (T.bv_of_binder b) in
      let br = (pat, v) in
      accu' `List.Tot.append` [br]
    | _ -> mk_tenum_branches ty vty v' accu' q
    end

let mk_function (t: T.term) (l: list T.branch) : T.Tac T.term =
  let b = T.fresh_binder t in
  let body = T.pack (T.Tv_Match (T.pack (T.Tv_Var (T.bv_of_binder b))) l) in
  T.pack (T.Tv_Abs b body)

let get_inductive_constructors (t: T.term) : T.Tac (list T.name) =
  let v : T.term_view = T.inspect t in
  match v with
  | T.Tv_FVar w ->
    let u = T.inspect_fv w in
    let env = T.cur_env () in
    let s : option T.sigelt = T.lookup_typ env u in
    if None? s then
      T.fail "No definition found"
    else begin
      let v : T.sigelt_view = T.inspect_sigelt (Some?.v s) in
      match v with
      | T.Sg_Inductive _ _ _ _ cts -> cts
      | _ -> T.fail "Not an inductive type"
    end
  | _ -> T.fail "Not a free variable"

let gen_synth' (t: T.term) (vt: T.term) : T.Tac T.term =
  let cts = get_inductive_constructors t in
  T.debug ("Inductive type with " ^ string_of_int (List.Tot.length cts));
  let f = mk_function t (mk_tenum_branches t vt 0 [] cts) in
  T.debug (T.term_to_string f);
  f

let gen_synth (t: T.term) : T.Tac unit =
  T.exact_guard (gen_synth' t (`U16.t));
  tconclude ()

let pat_of_term (t: T.term) : T.Tac T.pattern =
  let t = T.norm_term_env (T.cur_env ()) [delta; iota; primops] t in
  match T.inspect t with
  | T.Tv_Const v -> T.Pat_Constant v
  | T.Tv_FVar v -> T.Pat_Cons v []
  | _ -> T.fail "Not a pattern"

let term_of_pat (t: T.pattern) : T.Tac (option T.term) =
  match t with
  | T.Pat_Constant v -> Some (T.pack (T.Tv_Const v))
  | T.Pat_Cons v [] -> Some (T.pack (T.Tv_FVar v))
  | _ -> None

let rec invert_branches_with_cascade (enum_ty: T.term) (val_eq: T.term) (x: T.term) (accu: option T.term) (l: list T.branch) : T.Tac T.term =
  match l with
  | [] ->
    begin match accu with
    | None -> tfail "There must be at least one branch"
    | Some t -> t
    end
  | (p, t) :: q ->
    begin match term_of_pat p with
    | Some v ->
      let accu' = match accu with
      | None -> Some v
      | Some ac ->
        let scrut = T.mk_app val_eq [
          (x, T.Q_Explicit);
          (t, T.Q_Explicit);
        ]
        in
        Some (mk_if scrut enum_ty v ac)
      in
      invert_branches_with_cascade enum_ty val_eq x accu' q
    | _ -> invert_branches_with_cascade enum_ty val_eq x accu q
    end

let invert_function' (enum_ty val_ty: T.term) (teq: T.term) (f: T.term) : T.Tac T.term =
  match T.inspect f with
  | T.Tv_Abs b body ->
    begin match T.inspect body with
    | T.Tv_Match t br ->
      if T.term_eq t (T.pack (T.Tv_Var (T.bv_of_binder b)))
      then
        let bx = T.fresh_binder val_ty in
        let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
        T.pack (T.Tv_Abs bx (invert_branches_with_cascade enum_ty teq x None br))
      else T.fail "Not a function destructing on its argument"
    | _ -> T.fail "Not a match"
    end
  | _ -> T.fail "Not a function"

let tenum_bound_nat (t: T.term) : T.Tac nat =
  let c = get_inductive_constructors t in
  List.Tot.length c

let tenum_bound' (t: T.term) : T.Tac T.term =
  pack_nat (tenum_bound_nat t)

let tenum_bound (t: T.term) : T.Tac unit =
  T.exact (tenum_bound' t)

let gen_synth_bounded' (t: T.term) : T.Tac T.term =
  let bound = tenum_bound' t in
  let vt = T.mk_app (`bounded_u16) [bound, T.Q_Explicit] in
  gen_synth' t vt

let synth_inverse_forall_bounded_u16_pred
  (b: nat)
  (t: Type)
  (f1: (bounded_u16 b -> GTot t))
  (f2: (t -> GTot (bounded_u16 b)))
  (x: bounded_u16 b)
: GTot Type0
= f2 (f1 x) == x

let synth_inverse_forall_bounded_u16'
  (b: nat)
  (t: Type)
  (f1: (bounded_u16 b -> GTot t))
  (f2: (t -> GTot (bounded_u16 b)))
: GTot Type0
= forall_bounded_u16 b (synth_inverse_forall_bounded_u16_pred b t f1 f2)

val synth_inverse_forall_bounded_u16_intro
  (b: nat)
  (t: Type)
  (f1: (bounded_u16 b -> GTot t))
  (f2: (t -> GTot (bounded_u16 b)))
  (u: squash (synth_inverse_forall_bounded_u16' b t f1 f2))
: Tot (u' : squash (synth_inverse f2 f1))

let synth_inverse_forall_bounded_u16_intro b t f1 f2 u
= Classical.forall_intro (Classical.move_requires (forall_bounded_u16_elim b (synth_inverse_forall_bounded_u16_pred b t f1 f2)))

let synth_inverse_forall_tenum_solve' () : T.Tac unit =
  T.norm [delta; zeta; iota; primops];
  let x = tforall_intro () in
  T.destruct (T.pack (T.Tv_Var (T.bv_of_binder x)));
  to_all_goals (fun () ->
    let y = T.intro () in
    T.rewrite y;
    T.norm [delta; zeta; iota; primops];
    T.trivial ();
    T.qed ()
  )

let auto_squash_tm () : T.Tac T.term = T.pack (T.Tv_FVar (T.pack_fv ["Prims"; "auto_squash"]))

let synth_inverse_forall_tenum_solve () : T.Tac unit =
  let (hd, tl) = app_head_tail (T.cur_goal ()) in
  let auto_squash = auto_squash_tm () in
  if hd `T.term_eq` (`squash) || hd `T.term_eq` auto_squash
  then match tl with
  | [(g, _)] ->
    let (hd', _) = app_head_tail g in
    if hd' `T.term_eq` (`synth_inverse)
    then match T.trytac synth_inverse_forall_tenum_solve' with
    | Some _ -> ()
    | _ -> (T.dump "synth_inverse_forall_tenum_solve FAILED here:"; tfail "synth_inverse_forall_tenum_solve failed")
    else tfail "not a synth_inverse goal"
  | _ -> tfail "not enough arguments to squash"
  else tfail "not a squash"

let synth_inverse_forall_bounded_u16_solve'
  (b: T.term)
  (t: T.term)
  (f1: T.term)
  (f2: T.term)
: T.Tac unit =
  T.apply (T.mk_app (`(synth_inverse_forall_bounded_u16_intro)) [
    b, T.Q_Explicit;
    t, T.Q_Explicit;
    f1, T.Q_Explicit;
    f2, T.Q_Explicit;
  ]);
  let _ = T.divide 1 (fun () ->
    T.norm [delta; zeta; iota; primops];
    T.trivial ();
    tsuccess "synth_inverse_forall_bounded_u16_solve, main goal"
  ) (fun () ->
    tconclude ()
  )
  in
  tsuccess "synth_inverse_forall_bounded_u16_solve"

let synth_inverse_forall_bounded_u16_solve () : T.Tac unit =
  let (hd, tl) = app_head_tail (T.cur_goal ()) in
  let auto_squash = auto_squash_tm () in
  if hd `T.term_eq` (`squash) || hd `T.term_eq` auto_squash
  then match tl with
  | [(tl, _)] ->
    let (hd', tl') = app_head_tail tl in
    if hd' `T.term_eq` (`synth_inverse)
    then begin match tl' with
    | [ (t, _); (bt, _); (f2, _); (f1, _)] ->
      let (bt_hd, bt_tl) = app_head_tail bt in
      if bt_hd `T.term_eq` (`bounded_u16)
      then begin match bt_tl with
      | [(b, _)] ->
        synth_inverse_forall_bounded_u16_solve' b t f1 f2
      | _ -> tfail "not enough arguments to bounded_u16"
      end else
        let s = T.term_to_string bt in
        tfail ("value type " ^ s ^ " is not bounded_u16")
    | _ -> tfail "not enough arguments to synth_injective"
    end else tfail "Goal is not synth_injective"
  | _ -> tfail "Not enough arguments to squash"
  else tfail "Goal is not squash"

let gen_enum_specs (enum: T.term) : T.Tac (T.term * T.term) =
  let bound = tenum_bound' enum in
  let f = gen_synth_bounded' enum in
  let val_t = T.mk_app (`bounded_u16) [bound, T.Q_Explicit] in
  let val_eq = T.mk_app (`bounded_u16_eq) [bound, T.Q_Explicit] in
  let g = invert_function' enum val_t val_eq f in
  let pbound = T.mk_app (`parse_bounded_u16) [bound, T.Q_Explicit] in
  let sbound = T.mk_app (`serialize_bounded_u16) [bound, T.Q_Explicit] in
  let p' =
    T.mk_app (`parse_synth) [
      val_t, T.Q_Implicit;
      enum, T.Q_Implicit;
      pbound, T.Q_Explicit;
      g, T.Q_Explicit;
      f, T.Q_Explicit;
    ]
  in
  let s' =
    T.mk_app (`serialize_synth) [
      val_t, T.Q_Implicit;
      enum, T.Q_Implicit;
      pbound, T.Q_Implicit;
      sbound, T.Q_Explicit;
      g, T.Q_Explicit;
      f, T.Q_Explicit;
      (`()), T.Q_Explicit;
    ]
  in
  (p', s')


let gen_enum_parser' (enum: T.term) : T.Tac T.term =
  let (p', _) = gen_enum_specs enum in p'

let gen_enum_parser (pol: T.guard_policy) (enum: T.term) : T.Tac unit =
  T.exact_guard (gen_enum_parser' enum);
  according_to pol (fun () -> tconclude_with [
    synth_inverse_forall_bounded_u16_solve;
    synth_inverse_forall_tenum_solve;
  ])
