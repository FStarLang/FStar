open Prims
type real =
  | Real of Prims.string 
let (uu___is_Real : real -> Prims.bool) = fun projectee -> true
let (__proj__Real__item___0 : real -> Prims.string) =
  fun projectee -> match projectee with | Real _0 -> _0