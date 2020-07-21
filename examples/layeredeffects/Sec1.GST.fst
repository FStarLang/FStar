module Sec1.GST
let state = int
type tag = | R | RW
let op t0 t1 = match t0, t1 with _, RW | RW, _ -> RW | _ -> R
let gst (a:Type) (t:tag) =
  match t with
  | R -> (state -> a)
  | RW -> (state -> a * state)
let return a (x:a)
  : gst a R
  = fun s -> x
let lift_r_rw #a (g:gst a R)
  : gst a RW
  = fun (s:state) -> g s, s
let lift #a #t0 #t1 (g:gst a t0)
  : gst a (t0 `op` t1)
  = match t0,t1 with
    | R, RW -> lift_r_rw #a g
    | _ -> g
let bind_R #a #b (f:gst a R) (g: a -> gst b R)
  : gst b R
  = fun (s:state) ->
      let x = f s in
      g x s
let bind_RW #a #b (f:gst a RW) (g: a -> gst b RW)
  : gst b RW
  = fun (s:state) ->
      let x, s1 = f s in
      g x s1
let bind_homogeneous #a #b #t (f:gst a t) (g: a -> gst b t)
  : gst b t
  = match t with
    | R -> bind_R #a #b f g
    | RW -> bind_RW #a #b f g
let bind a b t0 t1 (f:gst a t0) (g: a -> gst b t1)
  : gst b (t0 `op` t1)
  = bind_homogeneous (lift f)
                     (fun (x:a) -> lift #_ #_ #t0 (g x))

let gst_read : gst state R = fun s -> s
let gst_write (s:state) : gst unit RW = fun _ -> (), s

reflectable
layered_effect {
  GST : a:Type -> tag -> Effect
  with
  repr = gst;
  return = return;
  bind = bind
}
let read () : GST state R = GST?.reflect gst_read
let write (s:state) : GST unit RW = GST?.reflect (gst_write s)
let u : Type = unit
let lift_pure a (x:u -> Tot a)
  : gst a R
  = fun (_:state) -> x()

sub_effect PURE ~> GST = lift_pure

let increment ()
  : GST unit RW
  = write (read () + 1)
