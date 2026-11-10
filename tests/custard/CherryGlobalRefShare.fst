module CherryGlobalRefShare

(* cherry.md, "References": until the program starts a thread, a global
   reference is read and written as a local one, so the value stored into it
   stays this thread's own.  [cherry_start_threads] shares what every global
   reference holds then, and from then on a value stored into one is shared
   as it is stored. *)

module U32 = FStar.UInt32
open FStar.All

[@@custard_extern "ext_is_shared"; custard_c_header "CherryGlobalRefShare_stubs.h"]
assume val is_shared : list string -> ML bool

[@@custard_extern "ext_start_threads"; custard_c_header "CherryGlobalRefShare_stubs.h"]
assume val start_threads : unit -> ML unit

private let r : ref (list string) = alloc []

let rec mk (n: nat) : ML (list string) =
  if n = 0 then [] else "x" :: mk (n - 1)

let main () : ML U32.t =
  r := mk 2;
  let before = is_shared !r in
  start_threads ();
  let after = is_shared !r in
  r := mk 3;
  let stored = is_shared !r in
  if not before && after && stored && List.length !r = 3 then 0ul else 1ul
