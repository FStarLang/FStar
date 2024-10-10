open FStarC_Compiler_Range
open Lexing

(* This brings into scope enough the translation of F# type names into the
 * corresponding OCaml type names; the reason for that is that we massage
 * parse.fsy (using sed) into parse.mly; but, we don't rename types. *)
include FStarC_BaseTypes
type single = float
type decimal = int
type bytes = byte array

let parseState = ()

let pos_of_lexpos (p:position) =
  mk_pos (Z.of_int p.pos_lnum) (Z.of_int (p.pos_cnum - p.pos_bol))

let mksyn_range (p1:position) p2 =
  mk_range p1.pos_fname (pos_of_lexpos p1) (pos_of_lexpos p2)

let translate_range (pos : Lexing.position * Lexing.position) =
  mksyn_range (fst pos) (snd pos)

let translate_range2 (pos1 : Lexing.position * Lexing.position) (pos2 : Lexing.position * Lexing.position) =
  mksyn_range (fst pos1) (snd pos2)

exception WrappedError of exn * range
exception ReportedError
exception StopProcessing

let warningHandler = ref (fun (e:exn) -> 
                          FStarC_Compiler_Util.print_string "no warning handler installed\n" ; 
                          FStarC_Compiler_Util.print_any e; ())
let errorHandler = ref (fun (e:exn) -> 
                        FStarC_Compiler_Util.print_string "no warning handler installed\n" ; 
                        FStarC_Compiler_Util.print_any e; ())
let errorAndWarningCount = ref 0
let errorR  exn = incr errorAndWarningCount; match exn with StopProcessing | ReportedError -> raise exn | _ -> !errorHandler exn
let warning exn = incr errorAndWarningCount; match exn with StopProcessing | ReportedError -> raise exn | _ -> !warningHandler exn

let comments : (string * FStarC_Compiler_Range.range) list ref = ref []
let add_comment x = comments := x :: !comments
let flush_comments () =
  let lexed_comments = !comments in
  comments := []; lexed_comments
