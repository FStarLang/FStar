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
module Log


(* Types of log levels *)
type loglevel =
  | Trace
  | Debug
  | Info
  | Warning
  | Error

(* Define information embedded in a facility *)
type facility = {
  name: string;
  level: list (loglevel);
  entries: list (loglevel * string * string);
  length: nat;
}

(* Create a log facility *)
assume val create: (name:string) -> loglevel -> facility

(* Delete an existing facility *)
assume val delete: facility -> unit

(* Retrieve an existing facility *)
assume val retrieve: (name:string) -> facility

(* Remove all the data from the facility *)
assume val clear: facility -> unit

(* Get a log entry *)
assume val get: facility -> nat -> loglevel * (name:string) * (value:string)

(* Remove the N last entries of the log *)
assume val trim: facility -> nat -> unit

(* Log a string at the required facility *)
assume val write: facility -> loglevel -> (name:string) -> (value:string) -> unit

(* Log a string at the required facility and to the dedicated std stream *)
assume val writeout: facility -> loglevel -> (name:string) -> (value:string) -> unit
