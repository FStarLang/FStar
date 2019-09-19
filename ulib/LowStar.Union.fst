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

let proj #key cases case u =
  u
#pop-options

/// An example
/// ==========

/// An example with a fictional type of messages, where some other information
/// in the context allows deducing the message and, hence, the particular case
/// of the union. Note that the invocation of ``union`` needs to be at the
/// top-level, and other occurrences of ``union`` are an extraction error.
type msg = | Msg1 | Msg2 | Msg3 | Msg4

/// Keyword probably needed for extraction to syntactically match on the
/// argument to union.
inline_for_extraction noextract
let msg_payload = [
  Msg1, ("fst_msg", int);
  Msg2, ("snd_msg", int & int)
]

/// The name (any_msg) and placement (right here) of the union typedef in C will
/// be determined via this top-level declaration.
let any_msg: one_of msg_payload -> Type =
  union msg_payload

/// The proof obligations here that Msg1 and Msg2 belong to msg_payload are
/// discharged by normalization.
let mk_msg (x: nat): any_msg (if x = 0 then Msg1 else Msg2) =
  if x = 0 then
    mk msg_payload Msg1 (-1)
  else
    mk msg_payload Msg2 (0, 0)

open FStar.Mul

let test (x: nat): int =
  let my_msg = mk_msg x in
  if x * x = 0 then
    proj msg_payload Msg1 my_msg
  else
    fst (proj msg_payload Msg2 my_msg)
