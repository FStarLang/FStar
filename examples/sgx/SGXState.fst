
module SGXState

open FStar.UInt64

let dword = UInt64.t

type register =
 | MkReg: string -> dword -> register

type cpuregstate =
 | Mkcpuregstate: (list register) -> cpuregstate

let get_reg_list = function
 |Mkcpuregstate li -> li

 

