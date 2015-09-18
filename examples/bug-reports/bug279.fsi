module Bug267

type t =
  | T : ts -> t
and ts = list t

val g: ts -> unit
