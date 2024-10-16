open Prims
let comment_gen : 't . Prims.string -> 't -> Prims.string -> 't =
  fun before -> fun body -> fun after -> body
let (comment : Prims.string -> unit) = fun s -> ()