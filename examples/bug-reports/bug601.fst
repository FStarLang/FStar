module Bug601

type ok (t:Type0) =
    | Good: ok t

assume type tp (t:Type0) : Type0

(* Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Name not found: StrangeTypePredicate.bad *)
type bad (t:Type0{tp t}) =
    | Bad: bad t

(* type pt = t:Type0{tp t} *)
(* type valid (t:pt) = *)
(*     | Valid: valid t *)
