module SteelTLArray

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.TLArray

noextract inline_for_extraction
let l = [0uy; 1uy]

let x = create l

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let i = get x 0ul in
  let j = get x 1ul in
  if i = j then return 1l else return 0l
