module Bug853b

open FStar.Heap
open FStar.ST

type state =
  | Open
  | Closed

type file = {name: string; state: state}

type isClosed file = (file.state) == Closed
type isOpen file = (file.state) == Open

val openHelper : f:file -> Pure file
    (requires (isClosed f))
    (ensures (fun f' -> isOpen f'))
let openHelper f =
    {name = f.name; state = Open}

let file1 = {
    name = "file1";
    state = Open;
}

let computeBase () =
    12

let read file =
    13

val readFromFile : file:file -> Pure unit
    (requires (isClosed file))
    (ensures (fun heap s heap' -> isClosed file heap'))
let readFromFile file =
    openHelper file;
    let x = computeBase () + read file in
    file.state := Closed

let nil () =
    readFromFile file1
