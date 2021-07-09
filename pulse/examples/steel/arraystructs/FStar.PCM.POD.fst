module FStar.PCM.POD

let pod a = option a

let none #a = None #a
let some x = Some (Ghost.reveal x)
let is_some v = match Ghost.reveal v with Some _ -> True | None -> False
let some_v x = match x with Some v -> v

let pod_pcm a = FStar.PCM.Extras.opt_pcm #a

let none_is_unit a = ()
let is_some_some v = ()
let some_none_distinct v = ()
let some_compatible v w = ()
let some_valid_write v w = ()
