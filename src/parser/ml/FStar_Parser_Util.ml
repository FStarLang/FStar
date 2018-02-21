open FStar_Range
open Lexing

(* This brings into scope enough the translation of F# type names into the
 * corresponding OCaml type names; the reason for that is that we massage
 * parse.fsy (using sed) into parse.mly; but, we don't rename types. *)
include FStar_BaseTypes
type single = float
type decimal = int
type bytes = byte array

let parseState = ()

let pos_of_lexpos (p:position) =
  mk_pos (Z.of_int p.pos_lnum) (Z.of_int (p.pos_cnum - p.pos_bol))

let mksyn_range (p1:position) p2 =
  mk_range p1.pos_fname (pos_of_lexpos p1) (pos_of_lexpos p2)

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
