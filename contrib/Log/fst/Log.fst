(*--build-config
  variables: LIB=../../../lib;
  options:--admit_fsi FStar.Set --admit_fsi FStar.Seq;
  other-files: $LIB/FStar.Classical.fst $LIB/FStar.FunctionalExtensionality.fst $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/FStar.All.fst
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
