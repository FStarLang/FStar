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

let pr  = Printf.printf
let fpr = Printf.fprintf
let spr = Printf.sprintf
let soi = string_of_int
let ios = int_of_string

let string_of_int (i:int):string = string_of_int i

let dummy = true

(* there must be a builtin F# func to lookup in assoc lists... *)
let rec lookup x l = match l with
  | [] -> failwith "lookup"
  | (k,v)::tl -> if k = x then v else lookup x tl

let findIdx x l =
  let rec f k = function
    | [] -> failwith "findIdx"
    | h::tl -> if h = x then k else f (k+1) tl
  in
  f 0 l

let trim s = String.trim [' '] s

let print_string (s:string) = let _ = Printf.printf "%s\n" s in 0
let strcat s1 s2 = s1 ^ s2
let strcat3 s1 s2 s3 = strcat s1 (strcat s2 s3)
