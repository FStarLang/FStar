module IO = Extlib.IO

module Unix = BatUnix
module Marshal = BatMarshal

open AST

type pchan_in = IO.input
type pchan_out = unit IO.output

let establish_server (callback:pchan_in -> pchan_out -> unit) (port:int) =
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  Unix.establish_server callback sock_addr

let read_input (c:pchan_in) :(prin * redex) = Marshal.input c

let write_output (out:pchan_out) (dv:dvalue) :unit = Marshal.output out dv

let create_thread (f:unit -> unit) :unit = let _ = Thread.create f () in ()
