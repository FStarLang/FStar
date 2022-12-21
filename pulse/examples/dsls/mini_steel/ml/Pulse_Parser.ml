let parse (s:string) =
  let lexbuf = Lexing.from_string s in
  Pulseparser.prog Pulselexer.token lexbuf
