module Bug279

type t =
  | T : list t -> t
type ts = list t

val g: ts -> unit
