module Pulse.Lib.InvList

open Pulse.Lib.Pervasives
module T0 = Pulse.Lib.Priv.Trade0

```pulse
unobservable
fn __shift_invlist_one
  (#a:Type0)
  (p : vprop)
  (i : inv p)
  (is : invlist{not (mem_inv (invlist_names is) i)})
  (#pre:vprop)
  (#post : a -> vprop)
  (f : unit -> stt_atomic a #Unobservable emp_inames (invlist_v (add_one (| p, i |) is) ** pre) (fun v -> invlist_v (add_one (| p, i |) is) ** post v))
  (_:unit)
  requires invlist_v is ** (p ** pre)
  returns v:a
  ensures invlist_v is ** (p ** post v)
{
  rewrite
    (p ** invlist_v is)
  as
    (invlist_v (add_one (|p, i|) is));
  let v = f ();
  rewrite
    (invlist_v (add_one (|p, i|) is))
  as
    (p ** invlist_v is);
  v
}
```
let shift_invlist_one = __shift_invlist_one

```pulse
unobservable
fn rec __with_invlist (#a:Type0) (#pre : vprop) (#post : a -> vprop)
  (is : invlist)
  (f : unit -> stt_atomic a #Unobservable emp_inames (invlist_v is ** pre) (fun v -> invlist_v is ** post v))
  requires pre
  returns v:a
  ensures post v
  opens (invlist_names is)
  decreases is
{
  match is {
    Nil -> {
      rewrite emp as invlist_v is;
      let r = f ();
      rewrite invlist_v is as emp;
      r
    }
    Cons h t -> {
      let p = dfst h;
      let i : inv p = dsnd h;
      with_invariants (i <: inv p) {
        assert (p ** pre);
        let fw : (unit -> stt_atomic a #Unobservable emp_inames (invlist_v t ** (p ** pre))
                (fun v -> invlist_v t ** (p ** post v))) = shift_invlist_one #a p i t #pre #post f;
        let v = __with_invlist #a #(p ** pre) #(fun v -> p ** post v) t fw;
        assert (p ** post v);
        v
      }
    }
  }
}
```
let with_invlist = __with_invlist

let lift_ghost_unobservable #pre #post (f:stt_ghost unit pre post) 
  : stt_atomic unit #Unobservable emp_inames pre post
  = lift_observability #_ #_ #Unobservable (lift_ghost_neutral f FStar.Tactics.Typeclasses.solve)

```pulse
unobservable
fn __with_invlist_ghost (#pre : vprop) (#post : vprop)
  (is : invlist)
  (f : unit -> stt_ghost unit (invlist_v is ** pre) (fun _ -> invlist_v is ** post))
  requires pre
  ensures post
  opens (invlist_names is)
{
  with_invlist is (fun () -> lift_ghost_unobservable (f ()));
}
```
let with_invlist_ghost = __with_invlist_ghost

let invlist_reveal = admit()

let iname_inj
  (p1 p2 : vprop)
  (i1 : inv p1) (i2 : inv p2)
  : stt_ghost unit
     (pure (name_of_inv i1 = name_of_inv i2))
     (fun _ -> pure (p1 == p2))
    = admit() // We should bubble this fact up from the memory model

let invlist_mem_split (i : iname) (is : invlist)
    (_ : squash (Set.mem i (invlist_names is)))
    : squash (exists l r p (ii : inv p).
              name_of_inv ii == i /\
              is == l @ [(| p, ii |)] @ r)
  = admit()

```pulse
ghost
fn __invlist_sub_split
  (is1 is2 : invlist) (_: squash (invlist_sub is1 is2))
  requires invlist_v is2
  ensures  invlist_v is1 ** T0.stick (invlist_v is1) (invlist_v is2)
{
  open T0;
  match is1 {
    Nil -> {
      ghost fn aux (_:unit)
        requires invlist_v is2 ** invlist_v is1
        ensures invlist_v is2
      {
        rewrite invlist_v is1 as emp;
        ();
      };
      intro_stick (invlist_v is1) (invlist_v is2) (invlist_v is2) aux;
      rewrite emp as invlist_v is1;
    }
    Cons h t -> {
      let p = dfst h;
      let i : inv p = dsnd h;
      let name = name_of_inv i;
      (* This is the interesting case, but it's rather hard to prove right now
      due to some pulse limitations (#151, #163). The idea is that (p, i) must
      also be in is2, so we can rewrite
           invlist_v is2
        ~> invlist_v (l @ [(|p, i|)] @ r)
        ~> p ** invlist_v (l @ r)

      and prove invlist_sub t (l@r), then we call the lemma recursively to obtain
          p ** invlist_v t ** stick (invlist_v t) (invlist_v (l@r))
        ~> invlist_v is1 ** stick (invlist_v t) (invlist_v (l@r))
      then we can 'frame' the stick with 'p' to get
        ~> invlist_v is1 ** stick (p ** invlist_v t) (p ** invlist_v (l@r))
        ~> invlist_v is1 ** stick is1 is2
      *)
      admit();
    }
  }
}
```

```pulse
ghost
fn __invlist_sub_split_wrap
  (is1 is2 : invlist)
  requires pure (invlist_sub is1 is2) ** invlist_v is2
  ensures  invlist_v is1 ** Pulse.Lib.Priv.Trade0.stick (invlist_v is1) (invlist_v is2)
{
  __invlist_sub_split is1 is2 ()
}
```
let invlist_sub_split = __invlist_sub_split_wrap
