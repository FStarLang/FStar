module Steel.C.Opt

module P = FStar.PCM
open Steel.C.PCM
open Steel.C.Ref
open Steel.Effect

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
: Steel b
    (r `pts_to` Some #b x)
    (fun _ -> r `pts_to` Some #b x)
    (requires fun _ -> True)
    (ensures fun _ x' _ -> Ghost.reveal x == x')

val opt_write
  (#a:Type) (#b:Type) (#x: Ghost.erased b)
  (r: ref a (opt_pcm #b)) (y: b)
: SteelT unit
    (r `pts_to` Some #b x)
    (fun _ -> r `pts_to` Some y)

let opt_view
  (a: Type)
: Tot (sel_view (opt_pcm #a) a false)
= {
  to_view_prop = (fun x -> Some? x == true);
  to_view = (fun x -> Some?.v x);
  to_carrier = (fun z  -> Some z);
  to_carrier_not_one = ();
  to_view_frame = (fun x frame -> ());
}

let exclusive_opt
  (#a: Type)
  (x: option a)
: Lemma
  (exclusive opt_pcm x <==> ((exists (y: a) . True) ==> Some? x))
=
  match x with
  | None ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (y: a). True)
    then begin
      let y = FStar.IndefiniteDescription.indefinite_description_ghost a (fun _ -> True) in
      assert (composable opt_pcm x (Some y))
    end else begin
      let phi
        (frame: option a)
      : Lemma
        (frame == None)
      = match frame with
        | None -> ()
        | Some z -> assert (exists (y: a) . True)
      in
      Classical.forall_intro phi
    end
  | Some _ -> ()

let opt_pcm_fpu
  (#a: Type)
  (x: Ghost.erased (option a) { ~ (Ghost.reveal x == one opt_pcm) })
  (y: a)
: Tot (frame_preserving_upd opt_pcm x (Some y))
= base_fpu opt_pcm x (Some y)

val opt_pcm_write
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b)) (y: b)
: Steel unit (r `pts_to` x) (fun _ -> r `pts_to` Some y)
  (requires (fun _ -> Some? x))
  (ensures (fun _ _ _ -> True))

val opt_pcm_read
  (#a:Type) (#b: Type)
  (r: ref a (opt_pcm #b)) (x: Ghost.erased (option b))
: Steel b (r `pts_to` x) (fun _ -> r `pts_to` x)
  (requires (fun _ -> Some? x))
  (ensures (fun _ y _ -> Ghost.reveal x == Some y))

let opt_read_sel
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a (opt_pcm #b))
: Steel b
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (opt_view b)) /\
    res == h' (pts_to_view r (opt_view b))
  ))
= ref_read_sel r (opt_view b)

let opt_write_sel
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a (opt_pcm #b))
  (w: b)
: Steel unit
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun _ _ h' ->
    w == h' (pts_to_view r (opt_view b))
  ))
=
  let _ = pts_to_view_elim r (opt_view _) in
  opt_pcm_write r _ w;
  pts_to_view_intro r _ (opt_view _) w

open Steel.C.Reference

let ref_opt_read
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a b (opt_pcm #b))
: Steel b
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (pts_to_view r (opt_view b)) /\
    res == h' (pts_to_view r (opt_view b))
  ))
= ref_read_sel r (opt_view b)

let ref_opt_write
  (#a: Type u#0) (#b: Type u#0)
  (r: ref a b (opt_pcm #b))
  (w: b)
: Steel unit
  (pts_to_view r (opt_view b))
  (fun _ -> pts_to_view r (opt_view b))
  (requires (fun _ -> True))
  (ensures (fun _ _ h' ->
    w == h' (pts_to_view r (opt_view b))
  ))
= opt_write_sel r w

val malloc
  (#c:Type0) (x: c)
: Steel (ptr (option c) c (opt_pcm #c))
    emp
    (fun r -> pts_to_view_or_null r (opt_view c))
    (requires fun _ -> True)
    (ensures fun _ r h' ->
      let s = h' (pts_to_view_or_null r (opt_view c)) in
      ptr_is_null r == None? s /\
      (Some? s ==> (Some?.v s == x /\ freeable r))
    )

val free
  (#c: Type0)
  (r: ref (option c) c (opt_pcm #c))
: Steel unit
    (pts_to_view r (opt_view c))
    (fun _ -> emp)
    (requires fun _ -> freeable r)
    (ensures fun _ _ _ -> True)
