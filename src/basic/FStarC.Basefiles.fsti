module FStarC.Basefiles

open FStarC.Compiler.Effect

val prims                       : unit    -> string
val prims_basename              : unit    -> string
val pervasives                  : unit    -> string
val pervasives_basename         : unit    -> string
val pervasives_native_basename  : unit    -> string
