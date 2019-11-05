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
module FStar.Getopt
open FSharp.Compatibility.OCaml
(* A simplified re-implementation of Getopt, a command line parsing tool *)
let noshort='\000'
let nolong=""

type opt_variant<'a> =
  | ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) * string

type opt'<'a> = char * string * opt_variant<'a> * string
type opt = opt'<unit>
type parse_cmdline_res =
  | Help
  | Error of string
  | Success

let bind l f =
    match l with
    | Help
    | Error _ -> l
    | Success -> f ()

(* Returns None if this wasn't an option arg (did not start with "-")
 * Otherwise, returns Some (o, s) where [s] is the trimmed option, and [o]
 * is the opt we found in specs (possibly None if not present, which should
 * trigger an error) *)
let find_matching_opt specs s : option<(option<opt> * string)> =
  if String.length s < 2 then
    None
  else if String.sub s 0 2 = "--" then
    (* long opts *)
    let strim = String.sub s 2 ((String.length s) - 2) in
    let o = List.tryFind (fun (_, option, _, _) -> option = strim) specs in
    Some (o, strim)
  else if String.sub s 0 1 = "-" then
    (* short opts *)
    let strim = String.sub s 1 ((String.length s) - 1) in
    let o = List.tryFind (fun (shortoption, _, _, _) -> FStar.String.make 1 shortoption = strim) specs in
    Some (o, strim)
  else
    None

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:list<opt>) def (ar:string []) ix max i =
  if ix > max then Success
  else
    let arg = ar.[ix] in
    let go_on () = let _ = def arg in parse opts def ar (ix + 1) max (i + 1) in
    match find_matching_opt opts arg with
    | None -> go_on ()
    | Some (None, _) -> Error ("unrecognized option '" + arg + "'\n")
    | Some (Some (_, _, p, _), argtrim) ->
      begin match p with
      | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
      | OneArg (f, _) ->
          if ix + 1 > max then Error ("last option '" + argtrim + "' takes an argument but has none\n")
          else
            let r =
                try (f (ar.[ix + 1]); Success)
                with _ -> Error ("wrong argument given to option '" + argtrim + "'\n")
            in bind r (fun () -> parse opts def ar (ix + 2) max (i + 1))
      end

let parse_array specs others args offset =
  parse specs others args offset (args.Length - 1) 0

let parse_cmdline specs others =
  let argv = System.Environment.GetCommandLineArgs() in
  if Array.length argv = 1 then Help
  else parse_array specs others argv 1

let parse_string specs others (str:string) =
    let split_spaces (str:string) =
        // F#'s str.Split will return empty strings when there's two spaces together
        // or at the boundaries. Filter them out, so we behave like OCaml
        let seps = [' '; '\t'] in
        Array.ofList <| (FStar.List.filter (fun s -> s <> "") <| FStar.String.split seps str)
    in
    let rec split_quoted_fragments (str:string) =
        let i = str.IndexOf '\'' in
        if i < 0 then Some (split_spaces str)
        else let prefix = str.Substring(0, i) in
             let suffix = str.Substring(i+1) in
             let j = suffix.IndexOf '\'' in
             if j < 0 then None
             else let quoted_frag = suffix.Substring(0, j) in
                  let rest = split_quoted_fragments (suffix.Substring(j+1))
                  match rest with
                  | None -> None
                  | Some rest -> Some (Array.append (split_spaces prefix)
                                                    (Array.append [| quoted_frag |] rest))
    in
    match split_quoted_fragments str with
    | None -> Error("Failed to parse options; unmatched quote \"'\"")
    | Some args ->
      parse_array specs others args 0

let cmdline () =
  let argv = System.Environment.GetCommandLineArgs() in
  List.ofArray argv
  
