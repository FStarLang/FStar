module LowStar.Union

#set-options "--max_fuel 0 --max_ifuel 0"


/// We want this helper to have a pattern, but only in the implementation, not
/// the interface.
#push-options "--max_fuel 1 --max_ifuel 1"
let rec existsb_assoc_some' (#a: eqtype) #b (x: a) (l: list (a & b)): Lemma
  (requires (List.Tot.existsb (find_fst x) l))
  (ensures (~(None? (List.Tot.assoc x l))))
  [ SMTPat (List.Tot.existsb (find_fst x) l) ]
=
  match l with
  | (x', _) :: xs ->
      if x <> x' then
        existsb_assoc_some' x xs
  | [] -> ()

let existsb_assoc_some = existsb_assoc_some'
#pop-options

#push-options "--max_fuel 1 --max_ifuel 1"
let union #key cases case =
  match List.Tot.assoc case cases with
  | Some t -> snd t

let mk #key cases case v =
  v

let proj #key cases case #label u =
  u
#pop-options
