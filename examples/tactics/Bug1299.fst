module Bug1299

open FStar.Tactics

let id () : Tac unit = ()

let failing () : Tac unit = fail "Uh oh" ()

let should_fail (t : tactic 'a) : tactic unit =
    r <-- trytac t;
    match r with
    | None -> idtac
    | Some _ -> fail "did not fail"

let make_term : tactic term =
  tt_tm <-- quote ();
  id_tm <-- quote id;
  failing_tm <-- quote failing;
  unit_tm <-- quote unit;
  let binder = fresh_binder unit_tm in
  return (pack (Tv_Abs binder (mk_app id_tm [(mk_app failing_tm [(tt_tm, Q_Explicit)], Q_Explicit)])))

let test : unit =
  assert_by_tactic True
    (should_fail (tm <-- make_term;
                  normalized_tm <-- norm_term [delta] tm;
                  t <-- unquote #(tactic unit) normalized_tm;
                  t))
