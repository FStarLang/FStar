(*
   Copyright 2008-2018 Microsoft Research

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
module LowStar.Printf

open FStar.Char
open FStar.String
module L = FStar.List.Tot
module LB = LowStar.Monotonic.Buffer
module I = FStar.Integers

irreducible
let __reduce__ = unit

noeq
type base_typ =
  | Bool
  | Char
  | U8
  | U16
  | U32
  | U64
  | I8
  | I16
  | I32
  | I64

noeq
type arg =
  | Base of base_typ
  | Array of base_typ

[@__reduce__]
let base_typ_as_type (b:base_typ) : Type0 =
  match b with
  | Bool   -> bool
  | Char   -> char
  | U8     -> FStar.UInt8.t
  | U16    -> FStar.UInt16.t
  | U32    -> FStar.UInt32.t
  | U64    -> FStar.UInt64.t
  | I8     -> FStar.Int8.t
  | I16    -> FStar.Int16.t
  | I32    -> FStar.Int32.t
  | I64    -> FStar.Int64.t

noeq
type fragment =
  | Frag of string
  | Interpolate of arg

let fragments = list fragment

let cons_char (c:char) (s:string) = string_of_list (c :: list_of_string s)

/// `parse_format s`:
///     Parses a list of characters into a list of directives
///     Or None, in case the format string is invalid
[@__reduce__]
let rec parse_format
      (s:list char)
 : Tot (option fragments)
       (decreases (L.length s))
 = let add_dir (d:arg) (ods : option fragments)
     = match ods with
       | None -> None
       | Some ds -> Some (Interpolate d::ds)
   in
   let head_buffer (ods:option fragments)
     = match ods with
       | Some (Interpolate (Base t) :: rest) -> Some (Interpolate (Array t) :: rest)
       | _ -> None
   in
   let cons_frag (c:char) (ods:option fragments)
     = match ods with
       | Some (Frag s::rest) -> Some (Frag (cons_char c s) :: rest)
       | Some rest -> Some (Frag (string_of_list [c]) :: rest)
       | _ -> None
   in
   match s with
   | [] -> Some []
   | ['%'] -> None

   // %x... arrays of base types
   | '%' :: 'x' :: s' -> 
     head_buffer (parse_format ('%' :: s'))

   // %u ... Unsigned integers
   | '%' :: 'u' :: s' -> begin
     match s' with
     | 'y' :: s'' -> add_dir (Base U8) (parse_format s'')
     | 's' :: s'' -> add_dir (Base U16) (parse_format s'')
     | 'l' :: s'' -> add_dir (Base U32) (parse_format s'')
     | 'L' :: s'' -> add_dir (Base U64) (parse_format s'')
     | _ -> None
     end

   | '%' :: c :: s' -> begin
     match c with
     | '%' ->  parse_format s'
     | 'b' -> add_dir (Base Bool)   (parse_format s')
     | 'c' -> add_dir (Base Char)   (parse_format s')
     | 's' -> None //TODO: LowStar.Literal.Const
     | 'y' -> add_dir (Base I8)     (parse_format s')
     | 'i' -> add_dir (Base I16)    (parse_format s')
     | 'l' -> add_dir (Base I32)    (parse_format s')
     | 'L' -> add_dir (Base I64)    (parse_format s')
     | _   -> None
     end

   | c :: s' ->
     cons_frag c (parse_format s')


/// `parse_format_string`: parses a format `string` into a list of directives
[@__reduce__]
let parse_format_string
    (s:string)
  : option fragments
  = parse_format (list_of_string s)

open FStar.HyperStack.ST
abstract
type lift (a:Type u#a) : Type u#(max a b) =
  | Lift : a -> lift a
  
let done : lift unit = Lift u#0 u#1 ()

[@__reduce__]
let rec interpret_args (l:fragments) (acc:list LB.buf_t) : Type u#1 =
  match l with
  | [] ->
     lift u#0 u#1 unit
    -> Stack unit
      (requires (fun h0 -> 
          FStar.BigOps.big_and' #LB.buf_t (fun (| _, _, _, b |) -> LB.live h0 b) acc))
      (ensures (fun h0 _ h1 -> h0 == h1))

  | Interpolate (Base t) :: args ->
    base_typ_as_type t ->
    interpret_args args acc

  | Interpolate (Array t) :: args ->
    l:UInt32.t -> 
    #r:_ ->
    #s:_ ->
    b:LB.mbuffer (base_typ_as_type t) r s ->
    interpret_args args (LB.buf b :: acc)

  | Frag _ :: args ->
    interpret_args args acc
    
unfold
let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm 
    [iota;
     zeta;
     delta_attr [`%__reduce__; `%BigOps.__reduce__];
     delta_only [`%Base?; `%Array?; `%Some?; `%Some?.v; `%list_of_string];
     primops;
     simplify]
     x

let elim_normal (x:bool) : Lemma (requires (normal #bool x)) (ensures x) = ()

let rec aux (frags:fragments) : interpret_args frags
val printf (s:string{normal #bool (Some? (parse_format_string s))})
  : normal (interpret_args (Some?.v (parse_format_string s)) [])
let printf s =
  let args = parse_format_string s in
  let rec aux a

let test (m:UInt64.t) (l:UInt32.t) (#r:_) (#s:_) (x:LB.mbuffer bool r s{LB.len x = l})
  : Stack unit
    (requires (fun h0 -> LB.live h0 x))
    (ensures (fun h0 _ h1 -> h0 == h1))
  = printf "%b%uL%xb" 
              true  //%b boolean
              m     //%uL u64
              l x   //%xb (buffer bool)
              done //dummy universe coercion
