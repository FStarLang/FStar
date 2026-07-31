open Prims
type ('a, 'b) optResult =
  | Error of 'a 
  | Correct of 'b 
let uu___is_Error (projectee : ('a, 'b) optResult) : Prims.bool=
  match projectee with | Error _0 -> true | uu___ -> false
let __proj__Error__item___0 (projectee : ('a, 'b) optResult) : 'a=
  match projectee with | Error _0 -> _0
let uu___is_Correct (projectee : ('a, 'b) optResult) : Prims.bool=
  match projectee with | Correct _0 -> true | uu___ -> false
let __proj__Correct__item___0 (projectee : ('a, 'b) optResult) : 'b=
  match projectee with | Correct _0 -> _0
let perror (file : Prims.string) (line : Prims.int) (text : Prims.string) :
  Prims.string= text
let correct (x : 'r) : ('a, 'r) optResult= Correct x
let rec unexpected : 'a . Prims.string -> 'a =
  fun s ->
    let uu___ =
      FStar_IO.debug_print_string
        (Prims.strcat "Platform.Error.unexpected: " s) in
    unexpected s
let rec unreachable : 'a . Prims.string -> 'a =
  fun s ->
    let uu___ =
      FStar_IO.debug_print_string
        (Prims.strcat "Platform.Error.unreachable: " s) in
    unreachable s
let if_ideal (f : unit -> 'a) (x : 'a) : 'a= x
