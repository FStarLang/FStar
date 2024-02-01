module Pulse.Lib.InvList

open Pulse.Lib.Pervasives

```pulse
unobservable
fn __shift_invlist_one
  (#a:Type0)
  (p : vprop)
  (i : inv p)
  (is : invlist{not (mem_inv (invlist_names is) i)})
  (#pre:vprop)
  (#post : a -> vprop)
  (f : unit -> stt_unobservable a emp_inames (invlist_v (add_one (| p, i |) is) ** pre) (fun v -> invlist_v (add_one (| p, i |) is) ** post v))
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
  (f : unit -> stt_unobservable a emp_inames (invlist_v is ** pre) (fun v -> invlist_v is ** post v))
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
        let fw : (unit -> stt_unobservable a emp_inames (invlist_v t ** (p ** pre)) (fun v -> invlist_v t ** (p ** post v))) = shift_invlist_one #a p i t #pre #post f;
        let v = __with_invlist #a #(p ** pre) #(fun v -> p ** post v) t fw;
        assert (p ** post v);
        v
      }
    }
  }
}
```
let with_invlist = __with_invlist

```pulse
unobservable
fn __with_invlist_ghost (#pre : vprop) (#post : vprop)
  (is : invlist)
  (f : unit -> stt_ghost unit emp_inames (invlist_v is ** pre) (fun _ -> invlist_v is ** post))
  requires pre
  ensures post
  opens (invlist_names is)
{
  with_invlist is (fun () -> lift_ghost_unobservable (f ()) (fun _ -> ()))
}
```
let with_invlist_ghost = __with_invlist_ghost

let invlist_reveal = admit()
