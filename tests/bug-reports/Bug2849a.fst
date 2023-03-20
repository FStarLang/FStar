module Bug2849a

module T = FStar.Tactics

let visit_terms (t: T.term): T.Tac unit =
  let rec tm (t: T.term): T.Tac unit = match T.inspect_unascribe t with
    | T.Tv_Match sc _ brs ->
      // do work then recurse...
      T.iter br brs;
      tm sc
    | _ -> ()
  and br (b: T.branch): T.Tac unit = tm (snd b)
  in tm t

let nothing (): unit =
  assert (true) by (
    visit_terms (`true)
  )
