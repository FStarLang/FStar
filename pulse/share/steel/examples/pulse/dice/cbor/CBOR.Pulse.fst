module CBOR.Pulse
include CBOR.Pulse.Extern
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Cbor = CBOR.Spec

noeq
type cbor_map_get_t =
| Found of cbor
| NotFound

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

let cbor_map_get_post_not_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
: Tot vprop
= raw_data_item_match p map vmap ** pure (
    Cbor.Map? vmap /\
    list_ghost_assoc vkey (Cbor.Map?.v vmap) == None
  )

let cbor_map_get_post_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists_ (fun vvalue ->
    raw_data_item_match p value vvalue **
    (raw_data_item_match p value vvalue @==> raw_data_item_match p map vmap) **
    pure (
      Cbor.Map? vmap /\
      list_ghost_assoc vkey (Cbor.Map?.v vmap) == Some vvalue
  ))

let cbor_map_get_post
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_post_not_found p vkey vmap map
  | Found value -> cbor_map_get_post_found p vkey vmap map value

let cbor_map_get_invariant
  (pmap: perm)
  (vkey: Ghost.erased Cbor.raw_data_item)
  (vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (i: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= match res with
  | Found value -> cbor_map_get_post_found pmap vkey vmap map value ** pure (
      Cbor.Map? vmap /\
      Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    )
  | NotFound ->
    cbor_map_iterator_match pmap i l **
    (cbor_map_iterator_match pmap i l @==> raw_data_item_match pmap map vmap) **
    pure (
        Cbor.Map? vmap /\
        list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap) ==
          list_ghost_assoc (Ghost.reveal vkey) l
    )

assume val elim_stick0
  (_: unit)
  (#hyp #concl: vprop)
: stt_ghost unit emp_inames
    ((hyp @==> concl) ** hyp)
    (fun _ -> concl)

assume val stick_refl0
    (p: vprop)
: stt_ghost unit emp_inames
    (emp)
    (fun _ -> p @==> p)


```pulse
ghost
fn cbor_map_get_invariant_end
  (pmap: perm)
  (vkey: Ghost.erased Cbor.raw_data_item)
  (vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor)
  (gres: Ghost.erased cbor_map_get_t)
  (res: cbor_map_get_t)
  (i: Ghost.erased cbor_map_iterator_t)
  (l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
requires
    cbor_map_get_invariant pmap vkey vmap map gres i l **
    pure (
        (Nil? l \/ Found? gres) /\
        res == Ghost.reveal gres
    )
ensures
    cbor_map_get_post pmap vkey vmap map res ** pure (
      Cbor.Map? vmap /\
      Found? res == Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    )
{
    match res
    {
        NotFound ->
        {
            rewrite (cbor_map_get_invariant pmap vkey vmap map gres i l) // FIXME: WHY WHY WHY?
                as (cbor_map_get_invariant pmap vkey vmap map NotFound i l);
            unfold (cbor_map_get_invariant pmap vkey vmap map NotFound i l);
            elim_stick0 ();
            fold (cbor_map_get_post_not_found pmap vkey vmap map);
            fold (cbor_map_get_post pmap vkey vmap map NotFound)
        }
        Found value ->
        {
            rewrite (cbor_map_get_invariant pmap vkey vmap map gres i l) // FIXME: WHY WHY WHY?
                as (cbor_map_get_invariant pmap vkey vmap map (Found value) i l);
            unfold (cbor_map_get_invariant pmap vkey vmap map (Found value) i l);
            fold (cbor_map_get_post pmap vkey vmap map (Found value))
        }
    }
}
```
assume
val stick_consume_l
    (_: unit)
    (#p #q #r: vprop)
: stt_ghost unit emp_inames
    (p ** ((p ** q) @==> r))
    (fun _ -> q @==> r)

assume
val stick_consume_r
    (_: unit)
    (#q #p #r: vprop)
: stt_ghost unit emp_inames
    (p ** ((q ** p) @==> r))
    (fun _ -> q @==> r)

assume
val stick_trans
    (_: unit)
    (#p #q #r: vprop)
: stt_ghost unit emp_inames
    ((p @==> q) ** (q @==> r))
    (fun _ -> p @==> r)

assume
val rewrite_with_implies
    (p q: vprop)
: stt_ghost unit emp_inames
    (p ** pure (p == q))
    (fun _ -> q ** (q @==> p))

assume
val stick_weaken_hyp_r
    (hl hr #hr' #c: vprop)
: stt_ghost unit emp_inames
    ((hr' @==> hr) ** ((hl ** hr) @==> c))
    (fun _ -> (hl ** hr') @==> c)

assume
val stick_weaken_hyp_l
    (hl hr #hl' #c: vprop)
: stt_ghost unit emp_inames
    ((hl' @==> hl) ** ((hl ** hr) @==> c))
    (fun _ -> (hl' ** hr) @==> c)

```pulse
fn cbor_map_get
  (key: cbor)
  (map: cbor)
  (#pkey: perm)
  (#pmap: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (#vmap: Ghost.erased Cbor.raw_data_item)
requires
    (raw_data_item_match pkey key vkey ** raw_data_item_match pmap map vmap ** pure (
      Cbor.Map? vmap /\
      (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey))
    ))
returns res: cbor_map_get_t
ensures
    (raw_data_item_match pkey key vkey ** cbor_map_get_post pmap vkey vmap map res ** pure (
      Cbor.Map? vmap /\
      Found? res == Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    ))
{
    let i0 = cbor_map_iterator_init map;
    with l0 . assert (cbor_map_iterator_match pmap i0 l0);
    let done0 = cbor_map_iterator_is_done i0;
    let mut pi = i0;
    let mut pres = NotFound;
    let mut pdone = done0;
    fold (cbor_map_get_invariant pmap vkey vmap map NotFound i0 l0);
    while (
        with gres i l . assert (pts_to pres gres ** pts_to pi i ** cbor_map_get_invariant pmap vkey vmap map gres i l);
        let res = !pres;
        let done = !pdone;
        assert (pts_to pres gres ** cbor_map_get_invariant pmap vkey vmap map gres i l); // FIXME: WHY WHY WHY?
        not (done || Found? res)
    )
    invariant cont . exists (done: bool) (res: cbor_map_get_t) (i: cbor_map_iterator_t) (l: list (Cbor.raw_data_item & Cbor.raw_data_item)) .
        raw_data_item_match pkey key vkey ** 
        pts_to pdone done **
        pts_to pi i **
        pts_to pres res **
        cbor_map_get_invariant pmap vkey vmap map res i l **
        pure (
            done == Nil? l /\
            cont == not (done || Found? res)
        )
    {
        with gres gi l . assert (pts_to pres gres ** cbor_map_get_invariant pmap vkey vmap map gres gi l);
        rewrite each gres as NotFound;
        unfold (cbor_map_get_invariant pmap vkey vmap map NotFound gi l);
        let x = cbor_map_iterator_next pi;
        stick_trans ();
        with gi' l'. assert (cbor_map_iterator_match pmap gi' l');
        with vx . assert (raw_data_item_map_entry_match pmap x vx);
        rewrite_with_implies
            (raw_data_item_map_entry_match pmap x vx)
            (raw_data_item_match pmap (cbor_map_entry_key x) (fstp vx) **
                raw_data_item_match pmap (cbor_map_entry_value x) (sndp vx)
            );
        let test = cbor_is_equal key (cbor_map_entry_key x);
        if (test) {
            stick_consume_l ()
                #(raw_data_item_match pmap (cbor_map_entry_key x) (fstp vx))
                #(raw_data_item_match pmap (cbor_map_entry_value x) (sndp vx));
            stick_weaken_hyp_l
                (raw_data_item_map_entry_match pmap x vx)
                (cbor_map_iterator_match pmap gi' l');
            stick_consume_r ()
                #(raw_data_item_match pmap (cbor_map_entry_value x) (sndp vx))
                #(cbor_map_iterator_match pmap gi' l');
            pres := Found (cbor_map_entry_value x);
            fold (cbor_map_get_post_found pmap vkey vmap map (cbor_map_entry_value x));
            fold (cbor_map_get_invariant pmap vkey vmap map (Found (cbor_map_entry_value x)) gi' l)
        } else {
            elim_stick0 ()
                #(raw_data_item_match pmap (cbor_map_entry_key x) (fstp vx) ** raw_data_item_match pmap (cbor_map_entry_value x) (sndp vx));
            stick_consume_l ()
                #(raw_data_item_map_entry_match pmap x vx)
                #(cbor_map_iterator_match pmap gi' l');
            let i' = !pi;
            rewrite each gi' as i';
            let done = cbor_map_iterator_is_done i';
            pdone := done;
            fold (cbor_map_get_invariant pmap vkey vmap map NotFound i' l')
        }
    };
    with gres i l . assert (pts_to pres gres ** cbor_map_get_invariant pmap vkey vmap map gres i l);
    let res = !pres;
    cbor_map_get_invariant_end pmap vkey vmap map gres res i l;
    res
}
```
