module FStar.Parser.Util
open FStar.Parser
open FStar.Parser.AST
open FStar
open FStar.Range

type bytes = byte[]
type decimal = System.Decimal

let pos_of_lexpos (p:Microsoft.FSharp.Text.Lexing.Position) =
    mk_pos p.Line p.Column

let mksyn_range (p1:Microsoft.FSharp.Text.Lexing.Position) p2 =
    mk_range p1.FileName (pos_of_lexpos p1) (pos_of_lexpos p2)

let getLexerRange (lexbuf:Microsoft.FSharp.Text.Lexing.LexBuffer<char>) = (* UnicodeLexing.Lexbuf) = *)
  mksyn_range lexbuf.StartPos lexbuf.EndPos

(* Get the range corresponding to the result of a grammar rule while it is being reduced *)
let lhs (parseState: Microsoft.FSharp.Text.Parsing.IParseState) =
  let p1,p2 = parseState.ResultRange in
  mksyn_range p1 p2

(* Get the position corresponding to the start of one of the r.h.s. symbols of a grammar rule while it is being reduced *)
let rhspos (parseState: Microsoft.FSharp.Text.Parsing.IParseState) n =
  pos_of_lexpos (fst (parseState.InputRange(n)))

(* /// Get the range covering two of the r.h.s. symbols of a grammar rule while it is being reduced *)
let rhs2 (parseState: Microsoft.FSharp.Text.Parsing.IParseState) n m =
  let p1 = parseState.InputRange(n) |> fst in
  let p2 = parseState.InputRange(m) |> snd in
  mksyn_range p1 p2

(* /// Get the range corresponding to one of the r.h.s. symbols of a grammar rule while it is being reduced *)
let rhs (parseState: Microsoft.FSharp.Text.Parsing.IParseState) n =
  let p1,p2 = parseState.InputRange(n) in
  mksyn_range p1 p2

let newline (lexbuf:Microsoft.FSharp.Text.Lexing.LexBuffer<_>) =
    lexbuf.EndPos <- lexbuf.EndPos.NextLine

let lexeme (lexbuf : Microsoft.FSharp.Text.Lexing.LexBuffer<char> (*UnicodeLexing.Lexbuf*)) =
    Microsoft.FSharp.Text.Lexing.LexBuffer<char> (*UnicodeLexing.Lexbuf*).LexemeString(lexbuf)
let ulexeme lexbuf = lexeme lexbuf

let adjust_lexbuf_start_pos (lexbuf:Microsoft.FSharp.Text.Lexing.LexBuffer<char> (*UnicodeLexing.Lexbuf*)) p =  lexbuf.StartPos <- p
