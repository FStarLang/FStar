
module SGXState

open FStar.UInt64
open Ast


type register =
 | MkReg: string -> dword -> register

type cpuregstate =
 | Mkcpuregstate: (list register) -> cpuregstate

val get_reg_list: cpuregstate -> Tot (list register)
let get_reg_list = function
 |Mkcpuregstate li -> li


