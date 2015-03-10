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
  let t =
    if z3v_le (get_z3version ()) (4, 3, 1)
    then !Options.z3timeout
    else !Options.z3timeout * 1000
  in
  let timeout = format1 "-t:%s" (string_of_int t) in
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
  let z3proc =
    let cond (s:string) = Util.trim_string s = "Done!" in
    Util.start_process (!Options.z3_exe) ini_params cond in
  let stdout = Util.ask_process z3proc input in    
  Util.kill_process z3proc;
  parse (Util.trim_string stdout) 

let get_qfile = 
    let ctr = Util.mk_ref 0 in
    fun () -> 
        incr ctr;
        Util.open_file_for_writing (Util.format1 "queries-%s.smt2" (Util.string_of_int !ctr))

let z3_options () =
  let mbqi =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "mbqi"
    else "smt.mbqi" in
  let model_on_timeout =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "(set-option :model-on-timeout true)\n"
    else ""
  in "(set-option :global-decls false)\n" ^
     "(set-option :" ^ mbqi ^ " false)\n" ^
     model_on_timeout

type job<'a> = {
    job:unit -> 'a;
    callback: 'a -> unit
}
type z3job = job<(bool * list<string>)>

let n_cores = 24
let n_runners = Util.mk_ref 0
let job_queue : ref<list<z3job>> = Util.mk_ref []

let z3_job label_messages input () =
  let status, lblnegs = doZ3Exe input in
  let result = match status with 
    | UNSAT -> true, []
    | _ -> 
        if !Options.debug <> [] then print_string <| format1 "Z3 says: %s\n" (status_to_string status);
        let failing_assertions = lblnegs |> List.collect (fun l -> 
        match label_messages |> List.tryFind (fun (m, _) -> fst m = l) with
            | None -> []
            | Some (_, msg) -> [msg]) in
        false, failing_assertions in        
    result

let rec dequeue () = 
    let next_job = atomically (fun () -> match !job_queue with 
        | [] -> None
        | hd::tl -> job_queue := tl; Some hd) in
    match next_job with 
        | None -> atomically (fun () -> decr n_runners)
        | Some j -> run_job j
and run_job j = 
    spawn (fun () -> j.callback <| j.job (); dequeue())

let enqueue j = 
    let n = atomically (fun () -> !n_runners) in 
    if n < n_cores
    then atomically (fun () -> incr n_runners; run_job j)
    else atomically (fun () -> job_queue := !job_queue@[j])

let rec finish () = 
    let n = atomically (fun () -> 
       let n = !n_runners in 
       if n=0 && List.length !job_queue <> 0
       then failwith "OUTSTANDING JOBS BUT NO RUNNERS!"
       else n) in
    if n=0 
    then Tc.Errors.report_all()
    else let _ = System.Threading.Thread.Sleep(500) in
         finish()

type scope_t = list<list<decl>>
let scope : ref<scope_t> = Util.mk_ref [[]]
let push msg    = scope := [Term.Caption msg]::!scope
let pop ()      = scope := List.tl !scope
let bgtheory () = List.rev !scope |> List.flatten
let giveZ3 decls = match !scope with 
    | hd::tl -> scope := (hd@decls)::tl
    | _ -> failwith "Impossible"
let ask label_messages qry cb =
  let log_query i = 
    let fh = get_qfile () in 
    Util.append_to_file fh i;
    Util.close_file fh in
  let theory = bgtheory()@qry in
  let input = List.map (declToSmt (z3_options ())) theory |> String.concat "\n" in
  if !Options.logQueries then log_query input; 
  enqueue ({job=z3_job label_messages input; callback=cb})
