(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.InvList

open Pulse.Lib.Pervasives
module T0 = Pulse.Lib.Priv.Trade0

```pulse
ghost
fn rec dup_invlist_inv (is:invlist)
  requires invlist_inv is
  ensures invlist_inv is ** invlist_inv is
  decreases is
{
  match is {
    Nil -> {
      rewrite invlist_inv is as emp;
      rewrite emp as invlist_inv is;
      rewrite emp as invlist_inv is
    }
    Cons h t -> {
      rewrite invlist_inv is as inv (snd h) (fst h) ** invlist_inv t;
      dup_invlist_inv t;
      dup_inv (snd h) (fst h);
      rewrite (inv (snd h) (fst h) ** invlist_inv t) as invlist_inv is;
      rewrite (inv (snd h) (fst h) ** invlist_inv t) as invlist_inv is
    }
  }
}
```

```pulse
ghost
fn shift_invlist_one
  (#a:Type0)
  (p : slprop)
  (i : iname)
  (is : invlist{not (mem_inv (invlist_names is) i)})
  (#pre:slprop)
  (#post : a -> slprop)
  (f : unit -> stt_ghost a emp_inames
                 (invlist_v (add_one ( p, i ) is) ** pre)
                 (fun v -> invlist_v (add_one ( p, i ) is) ** post v))
  (_:unit)
  requires invlist_v is ** (p ** pre)
  returns v:a
  ensures invlist_v is ** (p ** post v)
  opens emp_inames
{
  rewrite
    (p ** invlist_v is)
  as
    (invlist_v (add_one (p, i) is));
  let v = f ();
  rewrite
    (invlist_v (add_one (p, i) is))
  as
    (p ** invlist_v is);
  v
}
```

```pulse
ghost
fn rec with_invlist (#a:Type0) (#pre : slprop) (#post : a -> slprop)
  (is : invlist)
  (f : unit -> stt_ghost a emp_inames (invlist_v is ** pre) (fun v -> invlist_v is ** post v))
  requires invlist_inv is ** pre
  returns v:a
  ensures invlist_inv is ** post v
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
      rewrite (invlist_inv is) as (inv (snd h) (fst h) ** invlist_inv t);
      let r = with_invariants (snd h)
        returns v:a
        ensures inv (snd h) (fst h) ** invlist_inv t ** post v
        opens (add_inv (invlist_names t) (snd h)) {
        let fw : (unit -> stt_ghost a emp_inames
                            (invlist_v t ** (fst h ** pre))
                            (fun v -> invlist_v t ** (fst h ** post v))) = shift_invlist_one #a (fst h) (snd h) t #pre #post f;
        let v = with_invlist #a #((fst h) ** pre) #(fun v -> (fst h) ** post v) t fw;
        v
      };
      rewrite (inv (snd h) (fst h) ** invlist_inv t) as invlist_inv is;
      r
    }
  }
}
```

let invlist_reveal = admit()

```pulse
ghost
fn iname_inj
  (p1 p2 : slprop)
  (i1 i2 : iname)
  requires (inv i1 p1 ** inv i2 p2 ** pure (i1 = i2))
  ensures (inv i1 p1 ** inv i2 p2 ** pure (p1 == p2))
{
  invariant_name_identifies_invariant #p1 #p2 i1 i2;
  ()
}
```

let invlist_mem_split (i : iname) (is : invlist)
    (_ : squash (FStar.GhostSet.mem i (invlist_names is)))
    : squash (exists l r p (ii : iname).
              ii == i /\
              is == l @ [( p, ii )] @ r)
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
      let p = fst h;
      let i = snd h;
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
fn invlist_sub_split
  (is1 is2 : invlist)
  requires pure (invlist_sub is1 is2) ** invlist_v is2
  ensures  invlist_v is1 ** Pulse.Lib.Priv.Trade0.stick (invlist_v is1) (invlist_v is2)
{
  __invlist_sub_split is1 is2 ()
}
```


let invlist_sub_inv = admit ()
