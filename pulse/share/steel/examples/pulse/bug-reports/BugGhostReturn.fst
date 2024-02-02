module BugGhostReturn
open Pulse.Lib.Pervasives

assume
val extract (#a:Type) (x:squash a) : erased a

let pextract (#a:Type)
: stt_ghost (erased a) emp_inames (pure (squash a)) (fun _ -> emp)
= bind_sttg (elim_pure_explicit (squash a))
            (fun (x:squash a) -> 
                return_stt_ghost_noeq (extract x) (fun _ -> emp))

let join (#a:Type)
: Lemma (requires (squash (squash a)))
        (ensures (squash a))
        [SMTPat (squash (squash a))]
= ()        
// = FStar.Squash.join_squash #a ()

let psquash (a:Type u#a) : prop = squash a

```pulse
fn pextract' (#a:Type u#0)
requires pure (squash a)
returns i:erased a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = extract #a pf;
  i
}
```

assume
val p (#a:Type) (x:a) : prop

assume
val some_lemma (#a:Type) (x:a)
  : Lemma (p x)

```pulse
fn use_some_lemma (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}
```

// [@@expect_failure]
```pulse
ghost
fn use_some_lemma_ghost (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}
```