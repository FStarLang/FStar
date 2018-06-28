module MiniParse.Tac.Impl
include MiniParse.Tac.Base
include MiniParse.Impl.Combinators
include MiniParse.Impl.Int

module T = FStar.Tactics
module L = FStar.List.Tot
module TS = MiniParse.Tac.Spec

(* Generate the parser implementation from the parser specification *)

let rec gen_parser32' (p: T.term) : T.Tac T.term =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(parse_ret))
  then begin
    T.mk_app (`(parse32_ret)) tl
  end else
  if hd `T.term_eq` (`(parse_u8))
  then begin
    (`(parse32_u8))
  end else
  if hd `T.term_eq` (`(nondep_then))
  then match tl with
  | [k1; t1; (p1, _); k2; t2; (p2, _)] ->
    let p1' = gen_parser32' p1 in
    let p2' = gen_parser32' p2 in
    T.mk_app (`(parse32_nondep_then)) [
      k1;
      t1;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      k2;
      t2;
      (p2, T.Q_Implicit);
      (p2', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if hd `T.term_eq` (`(parse_synth))
  then match tl with
  | [k; qt1; t2; qp1; qf2] ->
    let (p1, _) = qp1 in
    let (t1, _) = qt1 in
    let (f2, _) = qf2 in
    let bx = T.fresh_binder t1 in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f2' = T.pack (T.Tv_Abs bx (T.mk_app f2 [x, T.Q_Explicit])) in
    let p1' = gen_parser32' p1 in
    T.mk_app (`(parse32_synth)) [
      k;
      qt1;
      t2;
      qp1;
      qf2;
      (f2', T.Q_Explicit);
      (p1', T.Q_Explicit);
      ((`()), T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to synth"
  else
  if hd `T.term_eq` (`(TS.package_parser))
  then match tl with
  | [qt; (pk, _)] ->
    let (hd', tl') = app_head_tail pk in
    if hd' `T.term_eq` (`(TS.mk_package))
    then match tl' with
    | [_; _; (p, _); _] ->
      gen_parser32' p
    | _ -> tfail "Not enough arguments to mk_package"
    else begin match T.inspect hd with
    | T.Tv_FVar v ->
      let env = T.cur_env () in
      let t' = T.norm_term_env env [iota] (T.mk_app (unfold_term hd') tl') in
      gen_parser32' (T.mk_app hd [qt; (t', T.Q_Explicit)])
    | _ -> tfail "Unknown parser package"
    end
  | _ ->
    tfail "Not enough arguments to package_parser"
  else
  match T.inspect hd with
  | T.Tv_FVar v ->
    let env = T.cur_env () in
    let t' = T.norm_term_env env [iota] (T.mk_app (unfold_term hd) tl) in
    gen_parser32' t'
  | _ ->
    tfail "Unknown parser combinator"

let p = parse_u8 `nondep_then` parse_ret 42

let gen_parser32 (p: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  T.exact_guard (gen_parser32' p);
  tconclude ()

let q : parser32 p = T.synth_by_tactic (fun () -> gen_parser32 (`(p)))

let p' = p `nondep_then` parse_u8

// let p' = (parse_u8 `nondep_then` parse_ret 42) `nondep_then` parse_u8

#push-options "--print_implicits"

let q' : parser32 p' = T.synth_by_tactic (fun () -> gen_parser32 (`(p')))

let r = parse_ret 42 `parse_synth` (fun x -> x + 1)

let r' : parser32 r = T.synth_by_tactic (fun () -> gen_parser32 (`(r)))

let j : parser _ TS.t = TS.package_parser TS.p

let j32 : parser32 j = T.synth_by_tactic (fun () -> gen_parser32 (`(j)))
