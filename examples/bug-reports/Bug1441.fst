module Bug1441

#set-options "--detail_errors"

val fail: n:int -> Lemma (n == 0)
let fail = function
  | 0 -> ()
  | _ -> ()

#reset-options

val falso: unit -> Lemma False
let falso _ = fail 1
