module MiniParse.Spec.TEnum
include MiniParse.Tac.Base

module T = FStar.Tactics
module U8 = FStar.UInt8

inline_for_extraction
let mk_u8 (n: nat { n < 256 } ) : Tot U8.t = U8.uint_to_t n

let rec mk_tenum_branches (ty: T.term) (vty: T.term) (v: nat) (accu: list T.branch) (l: list T.name) : T.Tac (list T.branch) =
  match l with
  | [] -> accu
  | n :: q ->
    let v' = v + 1 in
    let env = T.cur_env () in
    let v = T.mk_app (`(mk_u8)) [pack_nat v, T.Q_Explicit] in
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
  T.print ("Inductive type with " ^ string_of_int (List.Tot.length cts));
  let f = mk_function t (mk_tenum_branches t vt 0 [] cts) in
  T.print (T.term_to_string f);
  f

let gen_synth (t: T.term) : T.Tac unit =
  T.exact_guard (gen_synth' t (`U8.t));
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

let invert_function (enum_ty val_ty: T.term) (teq: T.term) (f: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  match T.inspect f with
  | T.Tv_FVar w ->
    let u = T.inspect_fv w in
    let env = T.cur_env () in
    let s = T.lookup_typ env u in
    if None? s
    then T.fail "No definition found"
    else begin
      match T.inspect_sigelt (Some?.v s) with
      | T.Sg_Let _ _ _ _ def ->
        let t = invert_function' enum_ty val_ty teq def in
        T.print (T.term_to_string t);
        T.exact_guard t;
        tconclude ()
      | _ -> T.fail "Not a let"
    end
  | _ -> T.fail "Not a global variable"

inline_for_extraction
let bounded_u8 (b: nat) : Tot eqtype = (x: U8.t { U8.v x < b } )

inline_for_extraction
let bounded_fun (a: Type) (b: nat) : Tot Type =
  a -> Tot (bounded_u8 b)

inline_for_extraction
let map_u8_to_bounded_u8
  (a: Type)
  (bound: nat)
  (f: (a -> Tot U8.t))
  (g: (x: a) -> Tot (squash (U8.v (f x) < bound)))
  (a' : Type)
  (bound' : nat)
  (u1: squash (a == a'))
  (u2: squash (bound == bound'))
: Tot (bounded_fun a' bound')
= fun x ->
  [@inline_let]
  let _ = g x in
  [@inline_let]
  let y' : bounded_u8 bound = f x in
  y'

let tenum_bound_nat (t: T.term) : T.Tac nat =
  let c = get_inductive_constructors t in
  List.Tot.length c

let tenum_bound' (t: T.term) : T.Tac T.term =
  pack_nat (tenum_bound_nat t)

let tenum_bound (t: T.term) : T.Tac unit =
  T.exact (tenum_bound' t)

let gen_synth_bounded (t: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  let bound = tenum_bound' t in
  let vt = T.mk_app (`bounded_u8) [bound, T.Q_Explicit] in
  T.exact_guard (gen_synth' t vt);
  tconclude ()

(*

let pred_pre
  (bound: nat { bound > 0 } )
  (pred: bounded_nat bound -> GTot Type0)
  (x: bounded_nat (bound - 1))
: GTot Type0
= pred (x + 1)

let rec forall_bounded_nat
  (bound: nat)
  (pred: (bounded_nat bound -> GTot Type0))
: GTot Type0
= if bound = 0
  then True
  else
    pred 0 /\ forall_bounded_nat (bound - 1) (pred_pre bound pred)

let rec forall_bounded_nat_elim
  (bound: nat)
  (pred: (bounded_nat bound -> GTot Type0))
  (x: bounded_nat bound)
: Lemma
  (requires (forall_bounded_nat bound pred))
  (ensures (pred x))
= if x = 0
  then ()
  else
    forall_bounded_nat_elim (bound - 1) (pred_pre bound pred) (x - 1)

module P = MiniParse.Spec.Combinators

let synth_injective_pred
  (b: nat)
  (t: Type)
  (f1: (bounded_nat b -> GTot t))
  (f2: (t -> GTot (bounded_nat b)))
  (x: bounded_nat b)
: GTot Type0
= f2 (f1 x) == x

let synth_injective'
  (b: nat)
  (t: Type)
  (f1: (bounded_nat b -> GTot t))
  (f2: (t -> GTot (bounded_nat b)))
: GTot Type0
= forall_bounded_nat b (synth_injective_pred b t f1 f2)

let synth_injective_intro
  (b: nat)
  (t: Type)
  (f1: (bounded_nat b -> GTot t))
  (f2: (t -> GTot (bounded_nat b)))
  (u: unit { synth_injective' b t f1 f2 } )
: Tot (u' : unit { P.synth_injective f1 } )
= Classical.forall_intro (Classical.move_requires (forall_bounded_nat_elim b (synth_injective_pred b t f1 f2)))
