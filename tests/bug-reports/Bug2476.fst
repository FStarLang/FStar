module Bug2476

open FStar.Tactics

assume val length_cons: #a:Type -> x:a -> l:list a -> Lemma (List.Tot.Base.length (x::l) == (List.Tot.Base.length l) + 1)

let test (h:int) (t:list int) =
  assert (List.Tot.Base.length (h::t) == List.Tot.Base.length t + 1) by (
    l_to_r [(`length_cons)];
    trefl()
  )
