module FStar_String
open Prims

let make (i : nat) (c : FStar_Char.char) = String.init (Microsoft.FSharp.Core.Operators.int i) (fun _ -> string([|c|]))
let strcat s t = s ^ t
let op_Hat s t =  strcat s t

let split (seps : FStar_Char.char list) (s : string) = s.Split(Array.ofList seps)
  
let compare (x : string) (y : string) = Prims.of_int (x.CompareTo(y)) 
type char = FStar_Char.char
let concat = String.concat
let length s = Prims.of_int (String.length s)
let strlen s = length s

let substring (s : string) (i : Prims.int) (j : Prims.int) = s.Substring(Microsoft.FSharp.Core.Operators.int i, Microsoft.FSharp.Core.Operators.int j)
let sub = substring

let get (s : string) (i : Prims.int) = s.[Microsoft.FSharp.Core.Operators.int i]
let collect (f : char -> string) (s : string) = s |> Array.ofSeq |> Array.map f |> String.concat ""
let lowercase (s : string) = s.ToLowerInvariant()
let uppercase (s : string) = s.ToUpperInvariant()
//let escaped = BatString.escaped
let index = get

let index_of (s : string) (c : char) = s.IndexOf(c) 
let list_of_string (s : string) = s |> Seq.toList 
let string_of_list (l : char list) = string(Array.ofList l)
let string_of_char (c : char) =  string(c, 1)
