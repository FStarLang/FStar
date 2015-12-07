(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --lax;
  other-files:ext.fst seq.fsi set.fsi heap.fst st.fst all.fst;
--*)

module ExtractionTest

type structure = | S: int -> char -> structure

type structure2 = {field1:int; field2:char}

type structure3 = 
  | S1: int -> char -> structure3
  | S2: int -> int -> structure3

val f: int -> Tot int
let f x = 2*x

val g: int -> char -> Tot char
let g x y =
  let z = x + x in
  let u = f z in
  let v = S x 'c' in
  let w = S2 x x in
  let s1 = S2._1 w in
  let b = is_S2 w in
  let w2 = { field1 = x; field2 = y } in
  let a = w2.field1 in
  y

val h: ref int -> ST structure3 (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let h x =
  let z = !x in
  let u = 
    match z with
    | 0 -> 1
    | 1 -> 1 in
  let vx = !x in
  let s = S2 vx 0 in
  s
  
val i: structure3 -> Tot int
let i s =
  let x = 
    match s with
    | S1 _ _ ->
      let res = S1._0 s in res
    | S2 _ _ ->
      let res = S2._1 s in res in
  x
