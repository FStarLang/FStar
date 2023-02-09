module MetaArgs

open FStar.Tactics
let sometac () : Tac unit = exact (`42)

let diag (x : int) (#[exact (quote x)] y : int) : tuple2 int int = (x, y)

val ee (#a: Type) (#[sometac()] dict: int) : unit
val ff (#a: Type) (#[sometac()] _: int) : unit
val gg: #a: Type -> #[sometac()] int -> unit
val ee': #a: Type -> _: int -> (#[sometac()] dict: int) -> int -> unit
val ff' (#a: Type) (_: int) (#[sometac()] _: int) (_: int) : unit
val gg': #a: Type -> int -> #[sometac()] int -> int -> unit
