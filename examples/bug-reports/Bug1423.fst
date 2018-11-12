module Bug1423

open FStar.List.Tot

val subset_filter: #a: eqtype -> f: (a -> Tot bool) -> l: list a ->
  Lemma (requires True) (ensures (subset (filter f l) l))
let subset_filter #_ f l =
  let rec aux l' = match l' with
  | [] -> ()
  | h :: t -> ()
  in aux (filter f l); admit ()
