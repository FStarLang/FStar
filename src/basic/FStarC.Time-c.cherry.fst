(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Time

(* The Cherry implementation: nanoseconds since the Unix epoch. *)

open FStarC.Effect
module U64 = FStar.UInt64

type time_of_day = U64.t

(* clock_gettime (CLOCK_REALTIME), in ulib/c/cherry.c. *)
[@@custard_extern "cherry_wall_ns"]
private assume val wall_ns : unit -> ML U64.t

(* stat's st_mtime in nanoseconds, or UINT64_MAX when stat fails. *)
[@@custard_extern "cherry_file_mtime_ns"]
private assume val file_mtime_ns : string -> ML U64.t

let get_time_of_day () = wall_ns ()

let get_time_of_day_ms () = U64.v (wall_ns ()) / 1000000

let is_before t1 t2 = U64.lt t1 t2

let get_file_last_modification_time fn =
  let t = file_mtime_ns fn in
  if t = 0xFFFFFFFFFFFFFFFFUL
  then failwith ("FStarC.Time.get_file_last_modification_time: cannot stat " ^ fn)
  else t

private let rec pad6 (s:string) (n:nat) : Tot string (decreases n) =
  if n = 0 then s else pad6 ("0" ^ s) (n - 1)

(* Seconds and microseconds: [1729371234.567890]. *)
let string_of_time_of_day t =
  let us = U64.v t / 1000 in
  let frac = string_of_int (us % 1000000) in
  let len = FStar.String.length frac in
  string_of_int (us / 1000000) ^ "." ^ pad6 frac (if len < 6 then 6 - len else 0)
