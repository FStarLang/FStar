module PCM.POD

let pod a = Ghost.erased (option a)

let none #a = Ghost.hide (None #a)
let some x = Ghost.hide (Some x)
let is_some v = match Ghost.reveal v with Some _ -> True | None -> False
let some_v x = match x with Some v -> v

let pod_pcm a = Aggregates.opt_pcm #a

let none_is_unit a = ()
let is_some_some v = ()
let some_none_distinct v = ()
let some_compatible v w = ()
let some_valid_write v w = ()
