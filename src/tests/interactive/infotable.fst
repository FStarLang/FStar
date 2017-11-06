module InfoTable

let x =
  let aaa: int = 111 in
  let bbb: string * int = "AAA", aaa in
  let ccc: nat * (string * int) = (123 <: nat), bbb in
  aaa, bbb, ccc
