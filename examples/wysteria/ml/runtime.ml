module IO = Extlib.IO

module Unix = BatUnix
module Marshal = BatMarshal

open Prins
open AST

type chan_in = IO.input
type chan_out = unit IO.output

let open_connection (port:int) :(chan_in * chan_out) =
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  Unix.open_connection sock_addr

let client_write (out:chan_out) (p:prin) (r:redex) :unit = Marshal.output ~closures:true out (p, r); IO.flush out
let client_read (c_in:chan_in) :dvalue =
  let v = Marshal.input c_in in
  IO.close_in c_in;
  v

let establish_server (callback:chan_in -> chan_out -> unit) (port:int) =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let sock_addr = Unix.ADDR_INET (Unix.inet_addr_of_string "127.0.0.1", port) in
  let _ = Unix.bind sock sock_addr in
  let _ = Unix.listen sock 10 in
  
  let rec accept_loop (_:unit) =
    let client_sock, _ = Unix.accept sock in
    let _ = callback (Unix.input_of_descr client_sock) (Unix.output_of_descr client_sock) in
    accept_loop ()
  in
  accept_loop ()  

let server_read (c:chan_in) :(prin * redex) = Marshal.input c
let server_write (out:chan_out) (dv:dvalue) :unit = Marshal.output ~closures:true out dv; IO.flush out; IO.close_out out
let create_thread (f:unit -> unit) :unit = let _ = Thread.create f () in ()

let is_server _ = Sys.argv.(1) = "0"
let me _ = Sys.argv.(2)


(**********)

exception GMWError of string

let gmwsock = ref Unix.stdin
let gmwsockset = ref false

let rungmw (conf_fname:string) (out_fname:string) (port:int) :unit =
  begin
    if not (!gmwsockset) then
      let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      let gmwaddr = Unix.ADDR_INET(Unix.inet_addr_of_string "127.0.0.1", port) in
      Unix.connect s gmwaddr;
      gmwsock := s; gmwsockset := true
    else ()
  end;

  let written = Unix.write !gmwsock conf_fname 0 (String.length conf_fname) in
  if not (written  = String.length conf_fname) then
    raise (GMWError "Cannot write to the main server socket")
  else
    let statusstr = String.make 5 '.' in
    let statusn = Unix.read !gmwsock statusstr 0 4 in
    assert(statusn = 4)
