open FStar_Range
open Lexing

type byte = char
type sbyte = char
type bytes = char array
type decimal = float
type single = float
type double = float
(* FIXME! *)
type int16 = Prims.int
type uint32 = Prims.int
type uint64 = Prims.int64

let parseState = ()

let pos_of_lexpos (p:position) =
  mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol)

let mksyn_range (p1:position) p2 =
  mk_file_idx_range (decode_file_idx p1.pos_fname) (pos_of_lexpos p1) (pos_of_lexpos p2)

let getLexerRange (lexbuf:lexbuf) =
  mksyn_range lexbuf.lex_start_p lexbuf.lex_curr_p

let lhs () =
  mksyn_range (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())

let rhs () n =
  mksyn_range (Parsing.rhs_start_pos n) (Parsing.rhs_end_pos n)

let rhspos () n =
  pos_of_lexpos (Parsing.rhs_start_pos n)

let rhs2 () n m =
  mksyn_range (Parsing.rhs_start_pos n) (Parsing.rhs_end_pos m)

exception WrappedError of exn * range
exception ReportedError
exception StopProcessing

let warningHandler = ref (fun (e:exn) -> 
                          FStar_Util.print_string "no warning handler installed\n" ; 
                          FStar_Util.print_any e; ())
let errorHandler = ref (fun (e:exn) -> 
                        FStar_Util.print_string "no warning handler installed\n" ; 
                        FStar_Util.print_any e; ())
let errorAndWarningCount = ref 0
let errorR  exn = incr errorAndWarningCount; match exn with StopProcessing | ReportedError -> raise exn | _ -> !errorHandler exn
let warning exn = incr errorAndWarningCount; match exn with StopProcessing | ReportedError -> raise exn | _ -> !warningHandler exn
