(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

module Microsoft.FStar.ToSMT.Z3
open Microsoft.FStar
open Microsoft.FStar.ToSMT.Term
open Microsoft.FStar.Util

(****************************************************************************)
(* Z3 Specifics                                                             *)
(****************************************************************************)
let ini_params = 
  format1 "/smt2 /in %s \
       AUTO_CONFIG=false \
       MBQI=false \
       MODEL=true \
       MODEL_ON_TIMEOUT=true \
       RELEVANCY=2 \
       ARRAY_DELAY_EXP_AXIOM=false \
       ARRAY_EXTENSIONAL=false" (match !Options.z3timeout with None -> "" | Some s -> format1 "/T:%s" (string_of_int <| (int_of_string s) / 1000))

type z3status = 
    | SAT 
    | UNSAT 
    | UNKNOWN 
    | TIMEOUT

let status_to_string = function
    | SAT  -> "sat"
    | UNSAT -> "unsat"
    | UNKNOWN -> "unknown"
    | TIMEOUT -> "timeout"

let doZ3Exe (input:string) = 
  let parse (z3out:string) = 
    let lines = String.split ['\n'] z3out |> List.map Util.trim_string in
    let rec lblnegs lines = match lines with 
      | lname::"false"::rest -> lname::lblnegs rest
      | lname::_::rest -> lblnegs rest
      | _ -> [] in
    let rec result x = match x with 
      | "timeout"::tl -> TIMEOUT, []
      | "unknown"::tl -> UNKNOWN, lblnegs tl
      | "sat"::tl -> SAT, lblnegs tl
      | "unsat"::tl -> UNSAT, []
      | _::tl -> result tl 
      | _ -> failwith <| format1 "Got output lines: %s\n" (String.concat "\n" (List.map (fun (l:string) -> format1 "<%s>" (Util.trim_string l)) lines)) in
      result lines in
  let cond (s:string) = Util.trim_string s = "Done!" in
  let z3proc = Util.start_process "z3.exe" ini_params cond in
  let stdout = Util.ask_process z3proc input in    
  let _ = Util.kill_all () in //process z3proc in
  parse (Util.trim_string stdout) 

let qfile = 
    let ctr = Util.mk_ref 0 in
    (fun () -> 
        incr ctr;
        let fname = format1 "query-%s.smt2" (string_of_int !ctr) in
        Util.print_string (Util.format1 "Writing to file %s\n" fname);
        fname)

let callZ3Exe (debug:bool) (theory:decls) labels = 
  let theory = labels |> List.fold_left (fun decls (lname, t) -> decls@[Echo lname; Eval t]) theory in
  let input = List.map declToSmt (theory@[Echo "Done!"]) |> String.concat "\n" in
    if debug then Util.write_file (qfile()) input; 
    let status, lblnegs = doZ3Exe input in
    match status with 
     | UNSAT -> true
     | _ -> 
       print_string <| format1 "Z3 says: %s\n" (status_to_string status);
       match status with 
         | UNKNOWN -> 
           print_string <| format1 "Failing assertions: %s\n" (String.concat "\n\t" lblnegs); false
         | _ -> 
           print_string <| format1 "Failing assertions: %s\n" (String.concat "\n\t" lblnegs); false 
