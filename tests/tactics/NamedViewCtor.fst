module NamedViewCtor

open FStar.Tactics.V2
module R = FStar.Reflection.V2

let not_unsupp (tv:term_view{~(Tv_Unsupp? tv)}) : Tot unit =
  let t = pack tv in
  assert (~(R.Tv_Unsupp? (R.inspect_ln t)))

let preserved (t1 t2 : term) : Tot unit =
  let t = pack (Tv_App t1 (t2, Q_Explicit)) in
  assert (R.Tv_App? (R.inspect_ln t))
