module PCM.POD

let pod a = option a

let none = None
let some = Some
let is_some v = match v with Some _ -> True | None -> False
let some_v (Some v) = v

let pod_pcm a = Aggregates.opt_pcm #a

let none_is_unit a = ()
let is_some_some v = ()
let some_none_distinct v = ()
let some_compatible v w = ()
let some_valid_write v w = ()
