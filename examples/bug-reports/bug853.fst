module Bug853

open FStar.Heap
open FStar.ST

type state =
  | Open
  | Closed

noeq type file = {name: string; state: ref state}

type isClosed file heap = (sel heap file.state) == Closed
type isOpen file heap = (sel heap file.state) == Open

val openHelper : file:file -> ST unit
    (requires (isClosed file))
    (ensures (fun heap s heap' -> isOpen file heap'))
let openHelper file =
    file.state := Open

let file1 () = {
    name = "file1";
    state = alloc Closed;
}

let computeBase () =
    12

let read file =
    13

val readFromFile : file:file -> ST unit
    (requires (isClosed file))
    (ensures (fun heap s heap' -> isClosed file heap'))
let readFromFile file =
    openHelper file;
    let x = computeBase () + read file in
    file.state := Closed

val nil : unit -> St unit
let nil () =
    readFromFile (file1 ())

(* let nil' = nil() *)
