module MiniParse.Tac.Spec
include MiniParse.Tac.Base
include MiniParse.Spec.Combinators
include MiniParse.Spec.Int

module T = FStar.Tactics
module L = FStar.List.Tot

noeq
type package (t: Type0) =
  | Package :
    (p: parser t) ->
    (s: serializer p) ->
    package t

let mk_package (#t: Type0) (#p: parser t) (s: serializer p) : Tot (package t) =
  Package p s

let package_parser (#t: Type0) (p: package t) : Tot (parser t) =
  Package?.p p

let package_serializer (#t: Type0) (p: package t) : Tot (serializer (package_parser p)) =
  Package?.s p

let rec gen_package' (p: T.term) : T.Tac (T.term * T.term) =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(FStar.UInt8.t))
  then begin
    ((`(parse_u8)), (`(serialize_u8)))
  end else
  if hd `T.term_eq` (`(tuple2))
  then match tl with
  | [(t1, _); (t2, _)] ->
    let (p1, s1) = gen_package' t1 in
    let (p2, s2) = gen_package' t2 in
    let p = T.mk_app (`(nondep_then)) [
      (t1, T.Q_Implicit);
      (p1, T.Q_Explicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Explicit);
    ]
    in
    let s = T.mk_app (`(serialize_nondep_then)) [
      (t1, T.Q_Implicit);
      (p1, T.Q_Implicit);
      (s1, T.Q_Explicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Implicit);
      (s2, T.Q_Explicit);
    ]
    in
    (p, s)
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if L.length tl = 0
  then begin
    gen_package' (unfold_term p)
  end else
    tfail "Unknown parser combinator"

let gen_package (t: T.term) : T.Tac unit =
  T.set_guard_policy T.Goal;
  let (p, s) = gen_package' t in
  let res = T.mk_app (`(mk_package)) [
    (t, T.Q_Implicit);
    (p, T.Q_Implicit);
    (s, T.Q_Explicit);
  ]
  in
  T.exact_guard res;
  tconclude ()

type u8 = FStar.UInt8.t

type t = (u8 * (u8 * u8))

let p : package t = T.synth_by_tactic (fun () -> gen_package (`t))
