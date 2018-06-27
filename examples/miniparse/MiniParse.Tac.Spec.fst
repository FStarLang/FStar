module MiniParse.Tac.Spec
include MiniParse.Tac.Base
include MiniParse.Spec.Combinators
include MiniParse.Spec.Int

module T = FStar.Tactics
module L = FStar.List.Tot

(* Generate the parser specification (and its kind) from the type *)

let rec gen_parser' (p: T.term) : T.Tac (T.term * T.term) =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(FStar.UInt8.t))
  then begin
    ((`(parse_u8_kind)), (`(parse_u8)))
  end else
  if hd `T.term_eq` (`(tuple2))
  then match tl with
  | [(t1, _); (t2, _)] ->
    let (k1, p1) = gen_parser' t1 in
    let (k2, p2) = gen_parser' t2 in
    let k = T.mk_app (`(and_then_kind)) [k1, T.Q_Explicit; k2, T.Q_Explicit] in
    let p = T.mk_app (`(nondep_then)) [
      (k1, T.Q_Implicit);
      (t1, T.Q_Implicit);
      (p1, T.Q_Explicit);
      (k2, T.Q_Implicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Explicit);
    ]
    in
    (k, p)
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if L.length tl = 0
  then begin
    gen_parser' (unfold_term p)
  end else
    tfail "Unknown parser combinator"

let gen_parser_kind (p: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  let (k, _) = gen_parser' p in
  T.exact k;
  T.qed ()

let gen_parser (p: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  let (_, p') = gen_parser' p in
  T.exact_guard p';
  tconclude ()

type u8 = FStar.UInt8.t

type t = (u8 * (u8 * u8))

let k : parser_kind = T.synth_by_tactic (fun () -> gen_parser_kind (`t))

let p : parser k t = T.synth_by_tactic (fun () -> gen_parser (`t))

