module FStar.Universe

(** This module implements some basic facilities to raise the universe of a type *
  * The type [raise_t a] is supposed to be isomorphic to [a] but in a higher     *
  * universe. The two functions [raise_val] and [dowgrade_val] allow to coerce   *
  * from [a] to [raise_t a] and back.                                            **)


(** [raise_t a] is an isomorphic copy of [a] (living in universe 'ua) in universe ['ub + 1] **)
val raise_t : Type 'ua -> Type u#(max 'ua ('ub + 1))

(** [raise_val x] injects a value [x] of type [a] to [raise_t a] **)
val raise_val : #a:Type 'ua -> x:a -> raise_t 'ua 'ub a

(** [downgrade_val x] projects a value [x] of type [raise_t a] to [a] **)
val downgrade_val : #a:Type 'ua -> x:raise_t 'ua 'ub a -> a
