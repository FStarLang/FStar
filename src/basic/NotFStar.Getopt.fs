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

(* remark: doesn't work with files starting with -- *)
let rec parse (opts:list<opt>) def (ar:string []) ix max i =
  if ix > max then Success
  else
    let arg = ar.[ix] in
    let go_on () = let _ = def arg in parse opts def ar (ix + 1) max (i + 1) in
      if String.length arg < 2 then
        go_on ()
      else
        let hd = String.sub arg 0 2 in
          if hd = "--" then
            let argtrim = String.sub arg 2 ((String.length arg) - 2) in
              match List.tryFind (fun (_, option, _, _) -> option = argtrim) opts with
                | Some (_, _, p, _) ->
                    (match p with
                       | ZeroArgs f -> f (); parse opts def ar (ix + 1) max (i + 1)
                       | OneArg (f, _) ->
                           if ix + 1 > max then Error ("last option '" + argtrim + "' takes an argument but has none\n")
                           else
                             let r =
                                 try (f (ar.[ix + 1]); Success)
                                 with _ -> Error ("wrong argument given to option '" + argtrim + "'\n")
                             in bind r (fun () -> parse opts def ar (ix + 2) max (i + 1)))
                | None -> Error ("unrecognized option '" + arg + "'\n")
          else go_on ()

let parse_cmdline specs others =
  let argv = System.Environment.GetCommandLineArgs() in
  let len = Array.length argv in
  let go_on () = parse specs others argv 1 (len - 1) 0 in
    if len = 1 then Help
    else go_on ()

let parse_string specs others (str:string) =
    let split_spaces (str:string) =
        // F#'s str.Split will return empty strings when there's two spaces together
        // or at the boundaries. Filter them out, so we behave like OCaml
        Array.filter (fun s -> s <> "") <| str.Split([|' ';'\t'|])
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
      parse specs others args 0 (args.Length - 1) 0
