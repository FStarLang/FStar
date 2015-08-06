open AST

exception Error of exn * (int * int * string)

module Lexer = Wlexer
module Parser = Wparser

let s = ""

let parse_channel :string -> in_channel -> unit =
  fun f i ->
  let lexbuf = Lexing.from_channel i in
  let _ = Parser.exp Lexer.token lexbuf in
  ()

let _ =
  let f = "example.wy" in
  let i = open_in f in
  let e = parse_channel f i in
  ()
;;

23
