module Seq = BatSeq
type 'a seq = 'a Seq.t

let length s = Seq.length s
let index s i = Seq.at s i

let create n x = Seq.make n x

let createEmpty = Seq.nil

let upd s n x =
  let prefix = Seq.take n s in
  let suffix = Seq.drop (n + 1) s in
  Seq.append prefix (Seq.cons x suffix)

let append s1 s2 =
  Seq.append s1 s2

let slice s i j =
  let sj = Seq.take s j in
  Seq.drop i sj
