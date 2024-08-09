module Bug2953

open FStar.Reflection
open FStar.Tactics.Effect

let f (t : term) : Tac (term) = t

noeq
type ty =  | A : bool -> term -> ty

[@@expect_failure [236]]
let open_view (tv:ty) : Tac unit =
  match tv with
  | A recf body when recf=false ->
    let _ : term = f body in
    ()
