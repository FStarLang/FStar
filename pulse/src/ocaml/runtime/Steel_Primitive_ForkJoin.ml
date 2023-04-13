type 'a thread = Thread.t

let fork (p:unit) (q:unit) (r:unit) (s:unit) (f:unit -> unit) (g:unit thread -> unit -> unit) =
  let t = Thread.create f () in
  g t ()

let join (t:unit thread) = Thread.join t
