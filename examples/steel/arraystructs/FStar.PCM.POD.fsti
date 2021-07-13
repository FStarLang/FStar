module FStar.PCM.POD

open FStar.PCM
open FStar.PCM.Extras
open AggregateRef
open Steel.Effect

let pod: Type u#a -> Type u#a = option

let none #a: Ghost.erased (pod a) = None

let some (x: Ghost.erased 'a): Ghost.erased (pod 'a) = Some (Ghost.reveal x)

let pod_pcm (a:Type): refined_one_pcm (pod a) = opt_pcm #a

val pod_read
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (r: ref a (pod_pcm b))
: Steel b
    (r `pts_to` some x)
    (fun _ -> r `pts_to` some x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> Ghost.reveal x == x')

val pod_write
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (r: ref a (pod_pcm b)) (y: b)
: SteelT unit
    (r `pts_to` some x)
    (fun _ -> r `pts_to` some (Ghost.hide y))
