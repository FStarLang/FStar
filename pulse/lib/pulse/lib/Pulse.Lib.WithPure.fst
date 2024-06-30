module Pulse.Lib.WithPure

open Pulse.Lib.Core
open Pulse.Main

// let tag (v:vprop) : vprop = v

let with_pure
  (p : prop)
  (v : squash p -> vprop)
: vprop
= op_exists_Star v
// Alternative definition:
// = exists* v'. tag v' ** pure (p /\ v' == v ())
// much easier to work with, but proving the size wasn't obvious.

let size_small
  (p : prop)
  (v : squash p -> vprop)
: Lemma (requires forall s. is_small (v s))
        (ensures  is_small (with_pure p v))
        [SMTPat (is_small (with_pure p v))]
= ()

let size_boxable
  (p : prop)
  (v : squash p -> vprop)
: Lemma (requires forall s. is_big (v s))
        (ensures  is_big (with_pure p v))
        [SMTPat (is_big (with_pure p v))]
= ()

let eta_exists_aux 
  (#a : Type0)
  (p : a -> vprop)
: vprop_equiv (op_exists_Star p) (op_exists_Star (fun (x:a) -> p x))
= let aux (x:a) : Lemma (vprop_equiv (p x) (p x)) =
    Squash.return_squash (vprop_equiv_refl (p x))
  in
  Classical.forall_intro aux;
  vprop_equiv_exists p (fun x -> p x) ()

let uneta_exists_aux 
  (#a : Type0)
  (p : a -> vprop)
: vprop_equiv (op_exists_Star (fun (x:a) -> p x)) (op_exists_Star p)
= let aux (x:a) : Lemma (vprop_equiv (p x) (p x)) =
    Squash.return_squash (vprop_equiv_refl (p x))
  in
  Classical.forall_intro aux;
  vprop_equiv_exists (fun x -> p x) p ()

```pulse
ghost
fn eta_exists
  (a : Type0)
  (p : a -> vprop)
  requires op_exists_Star p
  ensures  op_exists_Star (fun (x:a) -> p x)
{
  rewrite op_exists_Star p
       as op_exists_Star (fun (x:a) -> p x)
       by apply (`eta_exists_aux);
}
```

```pulse
ghost
fn uneta_exists
  (a : Type0)
  (p : a -> vprop)
  requires op_exists_Star (fun (x:a) -> p x)
  ensures  op_exists_Star p
{
  rewrite op_exists_Star (fun (x:a) -> p x)
       as op_exists_Star p
       by apply (`uneta_exists_aux);
}
```

```pulse
ghost
fn intro_with_pure
  (p : prop)
  (v : squash p -> vprop)
  (_ : squash p)
  requires pure p ** v ()
  ensures  with_pure p v
{
  assert (v ());
  assert (exists* s. v s);
  uneta_exists _ v;
  fold (with_pure p v);
}
```

```pulse
ghost
fn squash_single_coerce
  (p : prop)
  (v : squash p -> vprop)
  (s : squash p)
  requires v s
  ensures  pure p ** v ()
{
  rewrite v s as v ();
  ();
}
```

```pulse
ghost
fn elim_with_pure
  (p : prop)
  (v : squash p -> vprop)
  requires with_pure p v
  returns  s : squash p
  ensures  v ()
{
  unfold (with_pure p v);
  eta_exists _ v;
  with s. assert (v s);
  squash_single_coerce p v s;
  ()
}
```