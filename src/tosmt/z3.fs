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
type z3version =
| Z3V_Unknown
| Z3V of int * int * int

let z3v_compare known (w1, w2, w3) =
    match known with
    | Z3V_Unknown -> None
    | Z3V (k1, k2, k3) -> Some(
        if k1 <> w1 then w1 - k1 else
        if k2 <> w2 then w2 - k2 else
        w3 - k3
    )

let z3v_le known wanted =
    match z3v_compare known wanted with
    | None   -> false
    | Some i -> i >= 0

let _z3version : ref<option<z3version>> = Util.mk_ref None

let get_z3version () =
    let prefix = "Z3 version " in

    match !_z3version with
    | Some version -> version
    | None ->
        let _, out, _ = Util.run_proc !Options.z3_exe "-version" "" in
        let out =
            match splitlines out with
            | x :: _ when starts_with x prefix -> begin
                let x = trim_string (substring_from x (String.length prefix)) in
                let x = try List.map int_of_string (split x ".") with _ -> [] in
                match x with
                | [i1; i2; i3] -> Z3V (i1, i2, i3)
                | _ -> Z3V_Unknown
            end
            | _ -> Z3V_Unknown
        in
            _z3version := Some out; out

let ini_params =
  let timeout = format1 "-T:%s" (!Options.z3timeout)
  in

  let relevancy =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "RELEVANCY"
    else "SMT.RELEVANCY"
  in
  format2 "-smt2 -in %s \
    AUTO_CONFIG=false \
    MODEL=true \
    %s=2"
    timeout relevancy

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

let z3proc =
    let cond (s:string) = Util.trim_string s = "Done!" in
    Util.start_process (!Options.z3_exe) ini_params cond 

 

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
  let stdout = Util.ask_process z3proc input in    
  parse (Util.trim_string stdout) 

let qfh : ref<option<Util.file_handle>> = Util.mk_ref None
let get_qfile () = 
    match !qfh with 
        | Some f -> f
        | None -> 
          Util.print_string "Opening file queries.smt2\n";
          let fh = Util.open_file_for_writing "queries.smt2" in
          qfh := Some fh;
          fh

let cleanup () = 
    Util.kill_process z3proc;
    match !qfh with 
        | Some f -> Util.close_file f
        | _ -> ()

let batch : ref<decls> = Util.mk_ref []
let clear_batch () = let r = !batch in batch:=[]; r
let giveZ3 (theory:decls) = batch := !batch@theory
let queryZ3 label_messages (theory:decls)  =
  let theory = clear_batch()@theory in
  let input = List.map declToSmt theory |> String.concat "\n" in
    if !Options.logQueries then Util.append_to_file (get_qfile()) input; (* append flushes *)
    let status, lblnegs = doZ3Exe input in
    match status with 
        | UNSAT -> true, []
        | _ -> 
          if !Options.debug <> [] then print_string <| format1 "Z3 says: %s\n" (status_to_string status);
          let failing_assertions = lblnegs |> List.collect (fun l -> 
            match label_messages |> List.tryFind (fun (m, _) -> fst m = l) with
                | None -> []
                | Some (_, msg) -> [msg]) in
          false, failing_assertions
