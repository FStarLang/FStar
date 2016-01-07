(*--build-config
  variables: LIB=../../../lib;
  options:--admit_fsi FStar.Set --admit_fsi FStar.Seq;
  other-files: $LIB/classical.fst $LIB/ext.fst $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/FStar.All.fst
--*)
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
  level: loglevel;
  length: nat;
  entries: list string;
}

(* Create a log facility *)
assume val create: string -> loglevel -> facility

(* Delete an existing facility *)
assume val delete: facility -> unit

(* Retrieve an existing facility *)
assume val retrieve: string -> facility

(* Retrieve info about a facility *)
assume val info: facility -> string * loglevel * nat

(* Remove all the data from the facility *)
assume val clear: facility -> unit

(* Remove the N last entries of the log *)
assume val trim: facility -> nat -> unit

(* Log a string at the required facility *)
assume val write: facility -> string -> bool -> unit

(* Get the Nth entry of the log of a facility *)
assume val get: facility -> nat -> string
