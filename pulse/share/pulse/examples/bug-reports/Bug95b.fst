module Bug95b
#lang-pulse

open Pulse.Lib.Pervasives

let rec is_list_suffix
  (#t:Type) (x:ref t) (l:list t)
  : Tot slprop (decreases l)
  = match l with
    | [n] ->
      exists* (v:t).
        pts_to x v **
        pure (v == n)
    | _ -> emp


ghost
fn intro_is_list_singleton
  (#t:Type)
  (x : ref t) (n : t)
  requires
    exists* (v:t).
      pts_to x v **
      pure (v == n)
  ensures
    emp
{
  fold (is_list_suffix x [n]);
  admit();
}

