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
  | Some t -> t

let mk #key cases case v =
  v
#pop-options


/// An example with a fictional type of messages, where some other information
/// in the context allows deducing the message and, hence, the particular case
/// of the union. Note that the invocation of ``union`` needs to be at the
/// top-level, and other occurrences of ``union`` are an extraction error.
type msg = | Msg1 | Msg2 | Msg3 | Msg4

// JP: shouldn't we enforce pairwise disjoint here?
let msg_payload: list (msg & Type) = [ Msg1, int; Msg2, int & int ]

// Note that with sufficient fuel and ifuel we can write msg instead of one_of
// msg_payload. There is an exhaustivity argument; do we want to enforce it?
let any_msg: one_of msg_payload -> Type =
  union msg_payload

/// The proof obligations here that Msg1 and Msg2 belong to msg_payload are
/// discharged by normalization.
let mk_msg (x: nat): any_msg (if x = 0 then Msg1 else Msg2) =
  if x = 0 then
    mk msg_payload Msg1 (-1)
  else
    mk msg_payload Msg2 (0, 0)
