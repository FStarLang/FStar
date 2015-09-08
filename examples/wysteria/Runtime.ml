module IO = Extlib.IO

module Unix = BatUnix
module Marshal = BatMarshal

open AST

type chan_in = IO.input
type chan_out = unit IO.output

let open_connection (port:int) :(chan_in * chan_out) =
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  Unix.open_connection sock_addr

let client_write (out:chan_out) (p:prin) (r:redex) :unit = Marshal.output out (p, r)
let client_read (c_in:chan_in) :dvalue = Marshal.input c_in

let establish_server (callback:chan_in -> chan_out -> unit) (port:int) =
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  Unix.establish_server callback sock_addr

let server_read (c:chan_in) :(prin * redex) = Marshal.input c
let server_write (out:chan_out) (dv:dvalue) :unit = Marshal.output out dv
let create_thread (f:unit -> unit) :unit = let _ = Thread.create f () in ()

let is_server _ = Sys.argv.(1) = "0"
let me _ = Sys.argv.(2)

(* This is properly implemented in w-extraction branch *)
let get_smc = fun _ -> Exp ((E_const C_unit), None)
