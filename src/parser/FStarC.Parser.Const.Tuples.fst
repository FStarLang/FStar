(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR C  ONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Parser.Const.Tuples

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Range
open FStarC.Class.Show

// Arity, type constructor, and data constructor for tuples
private
let tuple_table : list (int & string & string) = [
  (2,  "FStar.Pervasives.Native.tuple2", "FStar.Pervasives.Native.Mktuple2");
  (3,  "FStar.Pervasives.Native.tuple3", "FStar.Pervasives.Native.Mktuple3");
  (4,  "FStar.Pervasives.Native.tuple4", "FStar.Pervasives.Native.Mktuple4");
  (5,  "FStar.Pervasives.Native.tuple5", "FStar.Pervasives.Native.Mktuple5");
  (6,  "FStar.Pervasives.Native.tuple6", "FStar.Pervasives.Native.Mktuple6");
  (7,  "FStar.Pervasives.Native.tuple7", "FStar.Pervasives.Native.Mktuple7");
  (8,  "FStar.Pervasives.Native.tuple8", "FStar.Pervasives.Native.Mktuple8");
  (9,  "FStar.Pervasives.Native.tuple9", "FStar.Pervasives.Native.Mktuple9");
  (10,  "FStar.Pervasives.Native.tuple10", "FStar.Pervasives.Native.Mktuple10");
  (11,  "FStar.Pervasives.Native.tuple11", "FStar.Pervasives.Native.Mktuple11");
  (12,  "FStar.Pervasives.Native.tuple12", "FStar.Pervasives.Native.Mktuple12");
  (13,  "FStar.Pervasives.Native.tuple13", "FStar.Pervasives.Native.Mktuple13");
  (14,  "FStar.Pervasives.Native.tuple14", "FStar.Pervasives.Native.Mktuple14");
]

let lookup_tuple n =
  match List.tryFind (fun (n', _, _) -> n = n') tuple_table with
  | Some r -> r
  | None ->
    failwith ("Tuple too large: " ^ (show n))

let mk_tuple_lid n r =
  let (_, s, _) = lookup_tuple n in
  let l = Ident.lid_of_str s in
  set_lid_range l r

let mk_tuple_data_lid n r =
  let (_, _, s) = lookup_tuple n in
  let l = Ident.lid_of_str s in
  set_lid_range l r

let get_tuple_datacon_arity (s:string) : option int =
  match List.tryFind (fun (_, _, s') -> s = s') tuple_table with
  | Some (n, _, _) -> Some n
  | None -> None
let get_tuple_tycon_arity (s:string) : option int =
  match List.tryFind (fun (_, s', _) -> s = s') tuple_table with
  | Some (n, _, _) -> Some n
  | None -> None

let is_tuple_constructor_string (s:string) : bool =
  List.existsb (fun (_, s', _) -> s = s') tuple_table

let is_tuple_datacon_string (s:string) : bool =
  List.existsb (fun (n, _, s') -> s = s') tuple_table

let is_tuple_constructor_lid lid = is_tuple_constructor_string (string_of_lid lid)
let is_tuple_datacon_lid lid = is_tuple_datacon_string (string_of_lid lid)
let is_tuple_data_lid f n = lid_equals f (mk_tuple_data_lid n dummyRange)

(* Dtuples *)

// Arity, type constructor, and data constructor for dependent tuples
private
let dtuple_table : list (int & string & string) = [
  (2, "Prims.dtuple2", "Prims.Mkdtuple2");
  (3, "FStar.Pervasives.dtuple3", "FStar.Pervasives.Mkdtuple3");
  (4, "FStar.Pervasives.dtuple4", "FStar.Pervasives.Mkdtuple4");
  (5, "FStar.Pervasives.dtuple5", "FStar.Pervasives.Mkdtuple5");
]

let lookup_dtuple n =
  match List.tryFind (fun (n', _, _) -> n = n') dtuple_table with
  | Some r -> r
  | None ->
    failwith ("DTuple too large: " ^ (show n))

let mk_dtuple_lid n r =
  let (_, s, _) = lookup_dtuple n in
  let l = Ident.lid_of_str s in
  set_lid_range l r

let mk_dtuple_data_lid n r =
  let (_, _, s) = lookup_dtuple n in
  let l = Ident.lid_of_str s in
  set_lid_range l r

let get_dtuple_datacon_arity (s:string) : option int =
  match List.tryFind (fun (_, _, s') -> s = s') dtuple_table with
  | Some (n, _, _) -> Some n
  | None -> None
let get_dtuple_tycon_arity (s:string) : option int =
  match List.tryFind (fun (_, s', _) -> s = s') dtuple_table with
  | Some (n, _, _) -> Some n
  | None -> None

let is_dtuple_constructor_string (s:string) : bool =
  List.existsb (fun (_, s', _) -> s = s') dtuple_table
let is_dtuple_datacon_string (s:string) : bool =
  List.existsb (fun (_, _, s') -> s = s') dtuple_table

let is_dtuple_constructor_lid lid = is_dtuple_constructor_string (string_of_lid lid)
let is_dtuple_data_lid f n = lid_equals f (mk_dtuple_data_lid n dummyRange)
let is_dtuple_datacon_lid f = is_dtuple_datacon_string (string_of_lid f)

let lid_tuple2   = mk_tuple_lid 2 dummyRange
let lid_tuple3   = mk_tuple_lid 3 dummyRange
let lid_tuple4   = mk_tuple_lid 4 dummyRange
let lid_tuple5   = mk_tuple_lid 5 dummyRange
let lid_Mktuple2 = mk_tuple_data_lid 2 dummyRange
let lid_Mktuple3 = mk_tuple_data_lid 3 dummyRange
let lid_Mktuple4 = mk_tuple_data_lid 4 dummyRange
let lid_Mktuple5 = mk_tuple_data_lid 5 dummyRange
let lid_dtuple2  = mk_dtuple_lid 2 dummyRange
