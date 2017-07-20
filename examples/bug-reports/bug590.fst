module Bug590

open FStar.List.Tot

let rec coerce (#a:Type) (ss:list (s:(list a){Cons? s}))
  : Pure (list (list a)) (requires True)
                         (ensures (fun ss' -> ss === ss')) =
  match ss with
  | [] -> let x : list (list a) = [] in admit() (* F* can't prove this? really? *)
  | h::t -> h :: (coerce t)

let flatten_lemma (a:Type) (ss:list (s:list a {Cons? s}) {Cons? ss}) :
  Lemma (requires True) (ensures (Cons? (flatten (coerce ss)))) = ()

(* original code *)
(* assume Flatten: forall (a:Type) (ss:list (s:list a) {Cons? ss}) . *)
(*     Cons? (flatten ss) *)

