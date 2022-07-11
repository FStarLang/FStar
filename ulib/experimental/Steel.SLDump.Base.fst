module Steel.SLDump.Base

include Steel.Effect.Common

[@@noextract_to "Plugin"]
let sldump_prop
  (text: string)
  (p: vprop)
  (q: vprop)
: Tot prop
= p == q

let sldump_prop_intro
  (text: string)
  (p: vprop)
: Lemma
  (sldump_prop text p p)
= ()

module T = FStar.Tactics

let solve_sldump_prop
  ()
: T.Tac bool
=
  let (hd, tl) = T.collect_app (T.cur_goal ()) in
  if not (hd `T.term_eq` (`squash) || hd `T.term_eq` (`auto_squash))
  then T.fail "not a squash goal";
  match tl with
  | [body1, T.Q_Explicit] ->
    let (hd1, tl1) = T.collect_app body1 in
    if not (hd1 `T.term_eq` (`sldump_prop))
    then T.fail "not a sldump_prop goal";
    begin match List.Tot.filter (fun (_, x) -> T.Q_Explicit? x) tl1 with
    | [(text, _); (p, _); (q, _)] ->
      let msg = match T.inspect text with
      | T.Tv_Const (T.C_String s) -> s
      | _ -> T.fail "not a constant string message"
      in
      if slterm_nbr_uvars p <> 0
      then T.fail "pre-resource not solved yet";
      let q_is_uvar = T.Tv_Uvar? (T.inspect q) in
      if not (q_is_uvar)
      then T.fail "sldump_prop is already solved";
      let p' = T.term_to_string p in
      T.print (msg ^ ": " ^ p');
      T.unshelve q;
      T.exact p;
      T.apply_lemma (`sldump_prop_intro);
      true
    | _ -> T.fail "ill-formed sldump_prop"
    end
  | _ -> T.fail "ill-formed squash"

[@@ resolve_implicits; framing_implicit; plugin;
    override_resolve_implicits_handler framing_implicit [`%Steel.Effect.Common.init_resolve_tac]]
let init_resolve_tac () = init_resolve_tac'
  [(`sldump_prop), solve_sldump_prop]
