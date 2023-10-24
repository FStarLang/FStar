module CDDL.Pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open CBOR.Spec
open CBOR.Pulse
open CDDL.Spec

module R = Pulse.Lib.Reference

inline_for_extraction noextract
let impl_typ
    (t: typ)
: Tot Type
=
    (c: cbor) ->
    (#v: Ghost.erased raw_data_item) ->
    stt bool
        (raw_data_item_match c v)
        (fun res -> raw_data_item_match c v ** pure (
            res == t v
        ))

inline_for_extraction noextract
let impl_bounded_typ
    (#b: raw_data_item)
    (t: bounded_typ b)
: Tot Type
=
    (c: cbor) ->
    (#v: Ghost.erased raw_data_item) ->
    stt bool
        (raw_data_item_match c v ** pure (
            Ghost.reveal v << b
        ))
        (fun res -> raw_data_item_match c v ** pure (
            Ghost.reveal v << b /\
            res == t v
        ))

inline_for_extraction noextract
let impl_array_group3
    (#b: raw_data_item)
    (g: array_group3 b)
: Tot Type
=
    (pi: R.ref cbor_array_iterator_t) ->
    (#i: Ghost.erased cbor_array_iterator_t) ->
    (#l: Ghost.erased (list raw_data_item)) ->
    stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match i l **
            pure (Ghost.reveal l << b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
            pure (
                Ghost.reveal l << b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
        )))

inline_for_extraction noextract
let eval_impl_array_group3
    (#b: Ghost.erased raw_data_item)
    (#g: array_group3 b)
    (ig: impl_array_group3 g)
    (pi: R.ref cbor_array_iterator_t)
    (#i: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
:   stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match i l **
            pure (Ghost.reveal l << Ghost.reveal b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
            pure (
                Ghost.reveal l << Ghost.reveal b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
        )))
= ig pi #i #l

assume val elim_stick0
  (_: unit)
  (#hyp #concl: vprop)
: stt_ghost unit emp_inames
    ((hyp @==> concl) ** hyp)
    (fun _ -> concl)

#push-options "--z3rlimit 32"

inline_for_extraction noextract
```pulse
fn impl_t_array
    (g: ((b: raw_data_item) -> array_group3 b))
    (ig: ((b: Ghost.erased raw_data_item) -> impl_array_group3 (g b)))
    (c: cbor)
    (#v: Ghost.erased raw_data_item)
requires
    raw_data_item_match c v
returns res: bool
ensures
    raw_data_item_match c v **
    pure (
        res == t_array3 g v
    )
{
    let ty = cbor_get_major_type c;
    if (ty = major_type_array) {
        let i = cbor_array_iterator_init c;
        with l . assert (cbor_array_iterator_match i l);
        rewrite (cbor_array_iterator_match i l) as (cbor_array_iterator_match (Ghost.reveal (Ghost.hide i)) l);
        let mut pi = i;
        let b_success = eval_impl_array_group3 (ig v) pi;
        with gi' l' . assert (cbor_array_iterator_match gi' l');
        let i' = ! pi;
        rewrite (cbor_array_iterator_match gi' l') as (cbor_array_iterator_match i' l');
        let b_end = cbor_array_iterator_is_done i';
        rewrite (cbor_array_iterator_match i' l') as (cbor_array_iterator_match gi' l');
        elim_stick0 ();
        rewrite (cbor_array_iterator_match (Ghost.reveal (Ghost.hide i)) l) as (cbor_array_iterator_match i l);
        elim_stick0 ();
        (b_success && b_end)
    } else {
        false
    }
}
```
