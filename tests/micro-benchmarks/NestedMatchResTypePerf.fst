module NestedMatchResTypePerf

/// A `match` is elaborated with an ascription of its own result type, and that
/// result type states, for each branch, an equation between the result and the
/// term the branch returns.  Written down naively the two refer to each other:
/// the term carries its type and the type carries the term, so a nest of n
/// matches is 2^n large.
///
/// `should_return` breaks the cycle by not stating the equation for a match
/// whose scrutinee is symbolic: such a match does not reduce, so the equation
/// tells the solver nothing it can use, and whatever the branches do establish
/// is already recorded in the match's result type.
///
/// The 12 `if`s below are 12 nested matches on a bool, under a match on a
/// list.  Without the cut this module takes hours to check; with it, a
/// fraction of a second.  The timeout in the Makefile is what makes this a
/// test.

assume val length (#a: Type) (l: list a) : nat

let byte = b: nat{b < 256}

assume val decode (l: list byte{Cons? l}) : r: list byte{length r < length l}

let decode_one (l: list byte) : option (r: list byte{length r < length l}) =
  match l with
  | [] -> None
  | b :: _ ->
    if b = 0 then Some (decode l)
    else if b = 1 then Some (decode l)
    else if b = 2 then Some (decode l)
    else if b = 3 then Some (decode l)
    else if b = 4 then Some (decode l)
    else if b = 5 then Some (decode l)
    else if b = 6 then Some (decode l)
    else if b = 7 then Some (decode l)
    else if b = 8 then Some (decode l)
    else if b = 9 then Some (decode l)
    else if b = 10 then Some (decode l)
    else if b = 11 then Some (decode l)
    else None
