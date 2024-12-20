module FStar_Ghost

type erased = unit
let reveal : erased -> unit = fun _ -> ()
let hide   : unit -> erased = fun  _ -> ()
let hide_reveal : erased -> unit = fun _ -> ()
let reveal_hide : unit -> unit = fun _ -> ()
let elift1   : (unit -> unit) -> erased -> erased = fun _ _ -> ()
let elift2   : (unit -> unit -> unit) -> erased -> erased -> erased = fun _ _ _ -> ()
let elift3   : (unit -> unit -> unit -> unit) -> erased -> erased -> erased -> erased = fun _ _ _ _ -> ()
let elift1_p : (unit -> unit) -> erased -> erased = fun _ _ -> ()
let elift2_p : (unit -> unit -> unit) -> erased -> erased -> erased = fun _ _ _ -> ()
