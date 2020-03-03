module Steel.Primitive.ForkJoin
open Steel.Effect
open Steel.Memory

val thread (p:hprop u#1) : Type u#0

val fork (#a:Type) (#p #q #r #s:hprop u#1)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)

val join (#p:hprop u#1) (t:thread p)
  : SteelT unit emp (fun _ -> p)
