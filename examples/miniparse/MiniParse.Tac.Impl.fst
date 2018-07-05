module MiniParse.Tac.Impl
include MiniParse.Tac.Base
include MiniParse.Impl.Combinators
include MiniParse.Impl.Int
include MiniParse.Impl.List
include MiniParse.Impl.TEnum

module T = FStar.Tactics
module L = FStar.List.Tot
module TS = MiniParse.Tac.Spec
module U32 = FStar.UInt32

inline_for_extraction
let mk_u32 (n: nat { n < 4294967296 } ) : Tot U32.t = U32.uint_to_t n

(* Generate the parser implementation from the parser specification *)

let rec gen_parser32' (p: T.term) : T.Tac T.term =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(parse_ret)) then T.mk_app (`(parse32_ret)) tl else
  if hd `T.term_eq` (`(parse_u8)) then (`(parse32_u8)) else
  if hd `T.term_eq` (`(nondep_then)) then match tl with
  | [t1; (p1, _); t2; (p2, _)] ->
    let p1' = gen_parser32' p1 in
    let p2' = gen_parser32' p2 in
    T.mk_app (`(parse32_nondep_then)) [
      t1;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      t2;
      (p2, T.Q_Implicit);
      (p2', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if hd `T.term_eq` (`(parse_synth))
  then match tl with
  | [qt1; t2; qp1; qf2; qg1] ->
    let (p1, _) = qp1 in
    let (t1, _) = qt1 in
    let (f2, _) = qf2 in
    let bx = T.fresh_binder t1 in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f2' = T.pack (T.Tv_Abs bx (T.mk_app f2 [x, T.Q_Explicit])) in
    let p1' = gen_parser32' p1 in
    T.mk_app (`(parse32_synth)) [
      qt1;
      t2;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      qf2;
      (f2', T.Q_Explicit);
      qg1;
      ((`()), T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to synth"
  else
  if hd `T.term_eq` (`parse_bounded_u8)
  then match tl with
  | [(b, _)] ->
    T.mk_app (`parse32_bounded_u8) [(b, T.Q_Explicit)]
  | _ -> tfail "not enough arguments to parse_bounded_u8"
  else
  if hd `T.term_eq` (`parse_filter)
  then match tl with
  | [(t, _); (p, _); (f, _)] ->
    let bx = T.fresh_binder t in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f' = T.pack (T.Tv_Abs bx (T.mk_app f [x, T.Q_Explicit])) in
    let p' = gen_parser32' p in
    T.mk_app (`parse32_filter) [
      (t, T.Q_Implicit);
      (p, T.Q_Implicit);
      (p', T.Q_Explicit);
      (f, T.Q_Explicit);
      (f', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to parse_filter"
  else
  if hd `T.term_eq` (`(TS.package_parser))
  then match tl with
  | [qt; (pk, _)] ->
    let (hd', tl') = app_head_tail pk in
    if hd' `T.term_eq` (`(TS.mk_package))
    then match tl' with
    | [_; (p, _); _] ->
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
  if hd `T.term_eq` (`parse_nlist)
  then match tl with
  | [(n, _); (t, _); (p, _)] ->
    let env = T.cur_env () in
    let tv = T.inspect (T.norm_term_env env [delta; iota; zeta; primops] n) in
    begin match tv with
    | T.Tv_Const (T.C_Int _) ->
      let n' = T.mk_app (`(mk_u32)) [T.pack tv, T.Q_Explicit] in
      let p' = gen_parser32' p in
      T.mk_app (`parse32_nlist) [
        (n, T.Q_Explicit);
        (n', T.Q_Explicit);
        (t, T.Q_Implicit);
        (p, T.Q_Implicit);
        (p', T.Q_Explicit);
      ]
    | _ -> tfail "parse_nlist: not an integer constant"
    end
  | _ -> tfail "Not enough arguments to parse_nlist"
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
  let t = gen_parser32' p in
  T.exact_guard t;
  tconclude_with [
    synth_inverse_forall_bounded_u8_solve;
    synth_inverse_forall_tenum_solve;
  ];
  T.print "gen_parser32 spits:";
  T.print (T.term_to_string t)

let q : parser32 p = T.synth_by_tactic (fun () -> gen_parser32 (`(p)))

let p' = p `nondep_then` parse_u8

// let p' = (parse_u8 `nondep_then` parse_ret 42) `nondep_then` parse_u8

#push-options "--print_implicits"

let q' : parser32 p' = T.synth_by_tactic (fun () -> gen_parser32 (`(p')))

let r : parser int =
  parse_synth
    (parse_ret 42)
    (fun x -> x + 1)
    (fun x -> x - 1)

let r' : parser32 r = T.synth_by_tactic (fun () -> gen_parser32 (`(r)))

let j : parser TS.t = TS.package_parser TS.p

let j32 : parser32 j = T.synth_by_tactic (fun () -> gen_parser32 (`(j)))
