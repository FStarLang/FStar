module IO = Extlib.IO

module Unix = BatUnix
module Marshal = BatMarshal

open AST

type pchan_in = IO.input
type pchan_out = unit IO.output

let open_connection (port:int) :(pchan_in * pchan_out) =
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  Unix.open_connection sock_addr

let write_input (out:pchan_out) (p:prin) (r:redex) :unit = Marshal.output out (p, r)

let read_output (c_in:pchan_in) :dvalue = Marshal.input c_in
