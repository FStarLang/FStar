module Steel.ST.C.Opt

module P = FStar.PCM
open Steel.ST.Util
open Steel.C.Model.PCM
open Steel.ST.C.Model.Ref

/// If no custom PCM is needed, p and q can be instantiated with an all-or-none PCM:

let opt_comp (x y: option 'a): prop = match x, y with
  | None, _ | _, None -> True
  | _, _ -> False

let opt_op (x: option 'a) (y: option 'a{opt_comp x y}): option 'a = match x, y with
  | None, z | z, None -> z

let fstar_opt_pcm #a : P.pcm (option a) = let open P in {
  p = {composable = opt_comp; op = opt_op; one = None};
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun x -> Some? x == true);
}

let opt_pcm #a : pcm (option a) = pcm_of_fstar_pcm fstar_opt_pcm

let option: Type u#a -> Type u#a = option

let none #a: Ghost.erased (option a) = None

[@@__reduce__]
let some (x: Ghost.erased 'a): Ghost.erased (option 'a) = Some (Ghost.reveal x)

let some_v (x: Ghost.erased (option 'a){Some? x}): Ghost.erased 'a = Some?.v x

val opt_read
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (r: ref a (opt_pcm #b))
: ST b
    (r `pts_to` Some #b x)
    (fun _ -> r `pts_to` Some #b x)
    (requires True)
    (ensures fun x' -> Ghost.reveal x == x')

val opt_write
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (r: ref a (opt_pcm #b)) (y: b)
: STT unit
    (r `pts_to` Some #b x)
    (fun _ -> r `pts_to` Some y)

val exclusive_opt
  (#a: Type)
  (x: option a)
: Lemma
  (exclusive opt_pcm x <==> ((exists (y: a) . True) ==> Some? x))

let opt_pcm_fpu
  (#a: Type)
  (x: Ghost.erased (option a) { ~ (Ghost.reveal x == one opt_pcm) })
  (y: a)
: Tot (frame_preserving_upd opt_pcm x (Some y))
= base_fpu opt_pcm x (Some y)

val opt_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b))
: ST b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (Some? x))
  (ensures (fun y -> Ghost.reveal x == Some y))

val opt_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: ST unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (Some? x))
  (ensures (fun _ -> True))
