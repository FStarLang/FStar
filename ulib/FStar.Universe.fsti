module FStar.Universe


(** This module implements some basic facilities to raise the universe of a type *
  * The type [raise_t a] is supposed to be isomorphic to [a] but in a higher     *
  * universe. The two functions [raise_val] and [dowgrade_val] allow to coerce   *
  * from [a] to [raise_t a] and back.                                            **)


(** [raise_t a] is an isomorphic copy of [a] (living in universe 'ua) in universe ['ub + 1] **)
val raise_t: Type u#a -> Type u#(max a (b + 1))

(** [raise_val x] injects a value [x] of type [a] to [raise_t a] **)
val raise_val: #a: Type u#a -> x: a -> raise_t u#a u#b a

(** [downgrade_val x] projects a value [x] of type [raise_t a] to [a] **)
val downgrade_val: #a: Type u#a -> x: raise_t u#a u#b a -> a

val downgrade_val_raise_val: #a: Type u#a -> x: a ->
  Lemma (downgrade_val u#a u#b (raise_val x) == x) [SMTPat (downgrade_val u#a u#b (raise_val x))]

val raise_val_downgrade_val: #a: Type u#a -> x: raise_t u#a u#b a ->
  Lemma (raise_val (downgrade_val x) == x) [SMTPat (raise_val u#a u#b (downgrade_val x))]

