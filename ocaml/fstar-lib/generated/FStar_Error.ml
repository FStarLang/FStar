open Prims
type ('a, 'b) optResult =
  | Error of 'a 
  | Correct of 'b 
let uu___is_Error : 'a 'b . ('a, 'b) optResult -> Prims.bool =
  fun projectee -> match projectee with | Error _0 -> true | uu___ -> false
let __proj__Error__item___0 : 'a 'b . ('a, 'b) optResult -> 'a =
  fun projectee -> match projectee with | Error _0 -> _0
let uu___is_Correct : 'a 'b . ('a, 'b) optResult -> Prims.bool =
  fun projectee -> match projectee with | Correct _0 -> true | uu___ -> false
let __proj__Correct__item___0 : 'a 'b . ('a, 'b) optResult -> 'b =
  fun projectee -> match projectee with | Correct _0 -> _0
let (perror : Prims.string -> Prims.int -> Prims.string -> Prims.string) =
  fun file -> fun line -> fun text -> text
let correct : 'a 'r . 'r -> ('a, 'r) optResult = fun x -> Correct x
let rec unexpected : 'a . Prims.string -> 'a = fun s -> unexpected s
let rec unreachable : 'a . Prims.string -> 'a = fun s -> unreachable s
let if_ideal : 'a . (unit -> 'a) -> 'a -> 'a = fun f -> fun x -> x
