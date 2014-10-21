(* -------------------------------------------------------------------- *)
exception ParseError of Lexing.position

let parse_error loc = raise (ParseError loc)
