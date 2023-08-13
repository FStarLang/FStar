module Example.RefineCase
open Pulse.Lib.Pervasives

noeq
type t = 
  | A : r:ref int -> t
  | B : r:ref bool -> t

type t_rep =
  | AR of int
  | BR of bool

let t_perm (x:t) (v:t_rep) : vprop =
    match x with
    | A r -> (
      match v with
      | AR i -> pts_to r i
      | _ -> pure False
    )
    | B r -> (
      match v with
      | BR b -> pts_to r b
      | _ -> pure False
    )

```pulse
ghost
fn elim_false (#a:Type0) (p: (a -> vprop))
    requires pure False
    returns x:a
    ensures p x
{
    let x = false_elim #a ();
    rewrite emp as (p x);
    x
}
```

//can't reveal in a match scrutinee yet
```pulse
ghost
fn refine (x:ref int) (v:erased t_rep)
  requires t_perm (A x) v
  returns i:erased int
  ensures pts_to x i ** pure (v == AR i)
{
   let u = reveal v;
   match u {
    AR i -> {
      rewrite (t_perm (A x) v)
          as  (pts_to x i);
      hide i
    }
    BR b -> {
      rewrite (t_perm (A x) v)
          as  (pure False);
      let x = elim_false #int (pts_to x);
      hide x
    }
  }
}
```

//Or this style
```pulse
ghost
fn refine_alt (x:ref int) (v:t_rep)
  requires t_perm (A x) v
  returns i:int
  ensures pts_to x i ** pure (v == AR i)
{
   match v {
    AR i -> {
      rewrite (t_perm (A x) v)
          as  (pts_to x i);
      i
    }
    BR b -> {
      rewrite (t_perm (A x) v)
          as  (pure False);
      elim_false (pts_to x)
    }
  }
}
```


```pulse
ghost
fn refine_ghost (x:ref int) (v:erased t_rep)
  requires t_perm (A x) v
  returns i:erased int
  ensures pts_to x i ** pure (v == AR i)
{
   let r = refine_alt x v;
   hide r
}
```
   

// assume
// val refine_ghost (x:ref int) (v:erased t_rep)
//   : stt_ghost (erased int) emp_inames
//     (requires t_perm (A x) v)
//     (ensures (fun i -> pts_to x i ** pure (reveal v == AR i)))
    