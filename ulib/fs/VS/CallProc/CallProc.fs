#light "off"

// Learn more about F# at https://fsharp.org
// See the 'F# Tutorial' project for more help.

open System
open System.IO
open System.Diagnostics
open System.Text.RegularExpressions

let quote_arg arg =
  let arg = Regex.Replace(arg, @"(\\*)" + "\"", @"$1$1\" + "\"") in
  "\"" + Regex.Replace(arg, @"(\\+)$", @"$1$1") + "\""

let quote_args args =
  String.concat " " (List.map quote_arg args)


let run_process (prog: string) (args: list<string>) : bool * string =
  let pinfo = new ProcessStartInfo(prog, quote_args args) in
  pinfo.RedirectStandardOutput <- true;
  pinfo.RedirectStandardError <- true;
  pinfo.UseShellExecute <- false;
  pinfo.RedirectStandardInput <- true;
  let proc = new Process() in
  proc.StartInfo <- pinfo;
  let result = proc.Start() in
  proc.StandardInput.Close();
  let stdout = proc.StandardOutput.ReadToEnd() in
  let stderr = proc.StandardError.ReadToEnd() in
  result, stdout + stderr

[<EntryPoint>]
let main argv =
    let args = List.ofArray argv in
    match args with
    | prog :: rest -> 
      let success, result = run_process prog rest in
      printfn "%A" result;
      if success then 0 else 1
    | _ -> 
      printfn "Not enough arguments";
      1
