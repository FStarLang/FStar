module Board

(* Common code sees the common interface of Uart only. *)
let board () : string = Uart.board
