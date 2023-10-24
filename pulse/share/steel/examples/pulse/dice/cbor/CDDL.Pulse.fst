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
let eval_impl_typ
    (#t: typ)
    (f: impl_typ t)
    (c: cbor)
    (#v: Ghost.erased raw_data_item)
:   stt bool
        (raw_data_item_match c v)
        (fun res -> raw_data_item_match c v ** pure (
            res == t v
        ))
= f c #v

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

module U8 = FStar.UInt8

noextract
let read_cbor_with_typ_success_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
=
    read_cbor_success_postcond va c v rem /\
    t v == true

module A = Pulse.Lib.Array

let read_cbor_with_typ_success_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match c.read_cbor_payload v **
    A.pts_to c.read_cbor_remainder #p rem **
    ((raw_data_item_match c.read_cbor_payload v ** A.pts_to c.read_cbor_remainder #p rem) @==>
      A.pts_to a #p va) **
    pure (read_cbor_with_typ_success_postcond t va c v rem)
  ))

noextract
let read_cbor_with_typ_error_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v .
    serialize_cbor v == Seq.slice va 0 (min (Seq.length (serialize_cbor v)) (Seq.length va)) ==>
    t v == false

let read_cbor_with_typ_error_postcond_intro_typ_fail
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: raw_data_item)
  (rem: Seq.seq U8.t)
: Lemma
    (requires (
        read_cbor_success_postcond va c v rem /\
        t v == false
    ))
    (ensures (
        read_cbor_with_typ_error_postcond t va
    ))
=
    let s = serialize_cbor v in
    let prf
        (v': raw_data_item)
    : Lemma
        (requires (serialize_cbor v' == Seq.slice va 0 (min (Seq.length (serialize_cbor v')) (Seq.length va))))
        (ensures (t v' == false))
    =
        let s' = serialize_cbor v' in
        Seq.lemma_split va (Seq.length s');
        serialize_cbor_inj v v' rem (Seq.slice va (Seq.length s') (Seq.length va))
    in
    Classical.forall_intro (Classical.move_requires prf)

let read_cbor_with_typ_error_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a #p va ** pure (read_cbor_with_typ_error_postcond t va)

let read_cbor_with_typ_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_cbor_with_typ_error_post t a p va
  | ParseSuccess c -> read_cbor_with_typ_success_post t a p va c

module SZ = FStar.SizeT

inline_for_extraction noextract
```pulse
fn read_cbor_with_typ
  (#t: typ)
  (ft: impl_typ t)
  (a: A.array U8.t)
  (sz: SZ.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
requires
    (A.pts_to a #p va ** pure (
      (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    ))
returns res: read_cbor_t
ensures read_cbor_with_typ_post t a p va res
{
    let res = read_cbor a sz;
    if (ParseSuccess? res) {
        let sres = ParseSuccess?._0 res;
        rewrite (read_cbor_post a p va res) as (read_cbor_success_post a p va sres);
        unfold (read_cbor_success_post a p va sres);
        let test = eval_impl_typ ft sres.read_cbor_payload;
        if (test) {
            fold (read_cbor_with_typ_success_post t a p va sres);
            rewrite (read_cbor_with_typ_success_post t a p va sres) as (read_cbor_with_typ_post t a p va res);
            res
        } else {
            with v . assert (raw_data_item_match sres.read_cbor_payload v);
            with vrem . assert (A.pts_to sres.read_cbor_remainder #p vrem);
            read_cbor_with_typ_error_postcond_intro_typ_fail t va sres v vrem;
            elim_stick0 ()
                #(raw_data_item_match sres.read_cbor_payload v ** A.pts_to sres.read_cbor_remainder #p vrem);
            fold (read_cbor_with_typ_error_post t a p va);
            rewrite (read_cbor_with_typ_error_post t a p va) as (read_cbor_with_typ_post t a p va ParseError);
            ParseError
        }
    } else {
        rewrite (read_cbor_post a p va res) as (read_cbor_error_post a p va);
        unfold (read_cbor_error_post a p va);
        fold (read_cbor_with_typ_error_post t a p va);
        rewrite (read_cbor_with_typ_error_post t a p va) as (read_cbor_with_typ_post t a p va res);
        res
    }
}
```
