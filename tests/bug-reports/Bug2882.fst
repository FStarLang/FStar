module Bug2882

open FStar.Tactics

let univ_uvar_to_term () : Tac unit =
  let t = fresh_uvar (Some (`unit)) in
  let tv = inspect_ln t in
  let _ = unify t (`()) in
  let tv' = inspect_ln t in
  assert (tv == tv');
  if not (Tv_Uvar? tv) || not (Tv_Uvar? tv') then
    fail "something changed!";
  ()

let go1 = assert True by univ_uvar_to_term ()

let unif_uvars () : Tac unit =
  let u1 = fresh_uvar (Some (`unit)) in
  let u2 = fresh_uvar (Some (`unit)) in
  match inspect_ln u1, inspect_ln u2 with
  | Tv_Uvar n1 _ , Tv_Uvar n2 _ ->
    let _ = unify u1 u2 in
    (match inspect_ln u1, inspect_ln u2 with
     | Tv_Uvar n1' _, Tv_Uvar n2' _ ->
       assert (n1 == n1' /\ n2 == n2');
       if n1 <> n1' then fail "n1 changed!";
       if n2 <> n2' then fail "n2 changed!";
       let _ = unify u1 (`()) in // to pass the test
       ()
    )
  | _ -> fail "impos"

let go2 = assert True by unif_uvars ()
