module CDDL.Pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick
open CBOR.Spec
open CBOR.Pulse
open CDDL.Spec

module R = Pulse.Lib.Reference

inline_for_extraction noextract
let impl_typ
    (#b: option raw_data_item)
    (t: bounded_typ_gen b)
: Tot Type
=
    (c: cbor) ->
    (#p: perm) ->
    (#v: Ghost.erased raw_data_item) ->
    stt bool
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) b
        ))
        (fun res -> raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) b /\
            res == t v
        ))

inline_for_extraction noextract
let eval_impl_typ
    (#b: Ghost.erased (option raw_data_item))
    (#t: bounded_typ_gen b)
    (f: impl_typ t)
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
:   stt bool
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
        (fun res -> raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
            res == t v
        ))
= f c #p #v

inline_for_extraction noextract
```pulse
fn impl_coerce_to_bounded_typ'
    (b: Ghost.erased (option raw_data_item))
    (#t: typ)
    (f: impl_typ t)
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
            res == coerce_to_bounded_typ b t v
        ))
{
    eval_impl_typ f c
}
```

inline_for_extraction noextract
let impl_coerce_to_bounded_typ
    (b: Ghost.erased (option raw_data_item))
    (#t: typ)
    (f: impl_typ t)
: Tot (impl_typ (coerce_to_bounded_typ b t))
= impl_coerce_to_bounded_typ' b f

inline_for_extraction noextract
```pulse
fn impl_t_choice'
    (#b: Ghost.erased (option raw_data_item))
    (#t1 #t2: bounded_typ_gen b)
    (f1: impl_typ t1)
    (f2: impl_typ t2)
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
            res == t_choice t1 t2 v
        ))
{
    let test = eval_impl_typ f1 c;
    if (test)
    {
        true
    } else {
        eval_impl_typ f2 c
    }
}
```

inline_for_extraction noextract
let impl_t_choice
    (#b: Ghost.erased (option raw_data_item))
    (#t1 #t2: bounded_typ_gen b)
    (f1: impl_typ t1)
    (f2: impl_typ t2)
: Tot (impl_typ (t_choice t1 t2))
= impl_t_choice' f1 f2

inline_for_extraction noextract
```pulse
fn impl_uint'
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item) /\
            res == uint v
        ))
{
    let mt = cbor_get_major_type c;
    (mt = major_type_uint64)
}
```
inline_for_extraction noextract
let impl_uint
: impl_typ uint
= impl_uint'

inline_for_extraction noextract
```pulse
fn impl_bytes'
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item) /\
            res == bytes v
        ))
{
    let mt = cbor_get_major_type c;
    (mt = major_type_byte_string)
}
```
inline_for_extraction noextract
let impl_bytes
: impl_typ bytes
= impl_bytes'

inline_for_extraction noextract
let impl_array_group3
    (#b: option raw_data_item)
    (g: array_group3 b)
: Tot Type
=
    (pi: R.ref cbor_array_iterator_t) ->
    (#p: perm) ->
    (#i: Ghost.erased cbor_array_iterator_t) ->
    (#l: Ghost.erased (list raw_data_item)) ->
    stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match p i l **
            pure (opt_precedes (Ghost.reveal l) b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            (cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
        )))

inline_for_extraction noextract
let eval_impl_array_group3
    (#b: Ghost.erased (option raw_data_item))
    (#g: array_group3 b)
    (ig: impl_array_group3 g)
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#i: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
:   stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match p i l **
            pure (opt_precedes (Ghost.reveal l) b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            (cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
        )))
= ig pi #p #i #l

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
fn intro_impl_array_group3_post
    (#b: option raw_data_item)
    (g: array_group3 b)
    (pi: R.ref cbor_array_iterator_t)
    (p: perm)
    (i: cbor_array_iterator_t)
    (l: list raw_data_item)
    (res: bool)
    (i': cbor_array_iterator_t)
    (l': list raw_data_item)
requires
    (
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            `@(cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
    )
ensures
        (exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            (cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
        )))

{
    ()
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

inline_for_extraction noextract
```pulse
fn impl_array_group3_concat'
    (#b: Ghost.erased (option raw_data_item))
    (#g1: array_group3 b)
    (f1: impl_array_group3 g1)
    (#g2: array_group3 b)
    (f2: impl_array_group3 g2)
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
requires
        (R.pts_to pi gi **
            cbor_array_iterator_match p gi l **
            pure (opt_precedes (Ghost.reveal l) (Ghost.reveal b))
        )
returns res: bool
ensures
        (exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            (cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p gi l) **
            pure (
                opt_precedes (Ghost.reveal l) (Ghost.reveal b) /\
                res == Some? (array_group3_concat g1 g2 l) /\
                (res == true ==> Some?.v (array_group3_concat g1 g2 l) == l')
            )
        )))
{
    let test1 = eval_impl_array_group3 f1 pi;
    if (test1) {
        let test2 = eval_impl_array_group3 f2 pi;
        stick_trans ();
        test2
    } else {
        false
    }
}
```

inline_for_extraction noextract
let impl_array_group3_concat
    (#b: Ghost.erased (option raw_data_item))
    (#g1: array_group3 b)
    (f1: impl_array_group3 g1)
    (#g2: array_group3 b)
    (f2: impl_array_group3 g2)
: Tot (impl_array_group3 (array_group3_concat g1 g2))
= impl_array_group3_concat' f1 f2

inline_for_extraction noextract
```pulse
fn impl_array_group3_item'
    (#b: Ghost.erased (option raw_data_item))
    (#ty: bounded_typ_gen b)
    (fty: impl_typ ty)
    (pi: R.ref cbor_array_iterator_t)
    (#p: perm)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
requires
        (R.pts_to pi gi **
            cbor_array_iterator_match p gi l **
            pure (opt_precedes (Ghost.reveal l) (Ghost.reveal b))
        )
returns res: bool
ensures
        (exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match p i' l' **
            (cbor_array_iterator_match p i' l' @==> cbor_array_iterator_match p gi l) **
            pure (
                opt_precedes (Ghost.reveal l) (Ghost.reveal b) /\
                res == Some? (array_group3_item ty l) /\
                (res == true ==> Some?.v (array_group3_item ty l) == l')
            )
        )))
{
    let i = !pi;
    rewrite (cbor_array_iterator_match p gi l) as (cbor_array_iterator_match p i l);
    let is_done = cbor_array_iterator_is_done i;
    rewrite (cbor_array_iterator_match p i l) as (cbor_array_iterator_match p gi l);
    if (is_done) {
        stick_refl0 (cbor_array_iterator_match p gi l);
        intro_impl_array_group3_post (array_group3_item ty) pi p gi l false gi l; // FIXME: WHY WHY WHY? and also WHY WHY WHY here and not in the other "false" case below?
        false
    } else {
        let c = cbor_array_iterator_next pi #p #l #gi; // FIXME: WHY WHY WHY those explicit arguments?
        with gc i' l' . assert (
            raw_data_item_match p c gc **
            cbor_array_iterator_match p i' l' **
            `@((raw_data_item_match p c gc ** cbor_array_iterator_match p i' l') @==> cbor_array_iterator_match p gi l)
        ); // this is needed for the explicit arguments to split_consume_l below
        let test = eval_impl_typ fty c;
        if (test) {
            stick_consume_l ()
                #(raw_data_item_match p c gc)
                #(cbor_array_iterator_match p i' l')
                #(cbor_array_iterator_match p gi l) // FIXME: WHY WHY WHY those explicit arguments? (for which the with above is needed)
            ;
            true
        } else {
            elim_stick0 ()
                #(raw_data_item_match p c gc ** cbor_array_iterator_match p i' l')
                #(cbor_array_iterator_match p gi l); // FIXME: WHY WHY WHY those explicit arguments?
            pi := i;
            rewrite (R.pts_to pi i) as (R.pts_to pi gi);
            stick_refl0 (cbor_array_iterator_match p gi l);
            false
        }
    }
}
```

inline_for_extraction noextract
let impl_array_group3_item
    (#b: Ghost.erased (option raw_data_item))
    (#ty: bounded_typ_gen b)
    (fty: impl_typ ty)
: Tot (impl_array_group3 (array_group3_item ty))
= impl_array_group3_item' fty

inline_for_extraction noextract
```pulse
fn impl_t_array'
    (#b: Ghost.erased (option raw_data_item))
    (g: (array_group3 b))
    (ig: (impl_array_group3 (g)))
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
    raw_data_item_match p c v **
    pure (opt_precedes (Ghost.reveal v) (Ghost.reveal b))
returns res: bool
ensures
    raw_data_item_match p c v **
    pure (
        opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
        res == t_array3 g v
    )
{
    let ty = cbor_get_major_type c;
    if (ty = major_type_array) {
        let i = cbor_array_iterator_init c;
        with l . assert (cbor_array_iterator_match p i l);
        rewrite (cbor_array_iterator_match p i l) as (cbor_array_iterator_match p (Ghost.reveal (Ghost.hide i)) l);
        let mut pi = i;
        let b_success = eval_impl_array_group3 ig pi;
        with gi' l' . assert (cbor_array_iterator_match p gi' l');
        let i' = ! pi;
        rewrite (cbor_array_iterator_match p gi' l') as (cbor_array_iterator_match p i' l');
        let b_end = cbor_array_iterator_is_done i';
        rewrite (cbor_array_iterator_match p i' l') as (cbor_array_iterator_match p gi' l');
        elim_stick0 ();
        rewrite (cbor_array_iterator_match p (Ghost.reveal (Ghost.hide i)) l) as (cbor_array_iterator_match p i l);
        elim_stick0 ();
        (b_success && b_end)
    } else {
        false
    }
}
```

inline_for_extraction noextract
let impl_t_array
    (#b: Ghost.erased (option raw_data_item))
    (#g: array_group3 b)
    (ig: impl_array_group3 g)
: Tot (impl_typ (t_array3 g))
= impl_t_array' g ig

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
    raw_data_item_match full_perm c.read_cbor_payload v **
    A.pts_to c.read_cbor_remainder #p rem **
    ((raw_data_item_match full_perm c.read_cbor_payload v ** A.pts_to c.read_cbor_remainder #p rem) @==>
      A.pts_to a #p va) **
    pure (read_cbor_with_typ_success_postcond t va c v rem)
  ))

noextract
let read_cbor_with_typ_error_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff .
    Ghost.reveal va == serialize_cbor v `Seq.append` suff ==>
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
= serialize_cbor_with_test_correct v rem (fun v' rem' -> t v' == true)

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
            with v . assert (raw_data_item_match full_perm sres.read_cbor_payload v);
            with vrem . assert (A.pts_to sres.read_cbor_remainder #p vrem);
            read_cbor_with_typ_error_postcond_intro_typ_fail t va sres v vrem;
            elim_stick0 ()
                #(raw_data_item_match full_perm sres.read_cbor_payload v ** A.pts_to sres.read_cbor_remainder #p vrem);
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
noextract
let read_deterministically_encoded_cbor_with_typ_success_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
=
    read_deterministically_encoded_cbor_success_postcond va c v rem /\
    t v == true

noextract
let read_deterministically_encoded_cbor_with_typ_error_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff .
    (Ghost.reveal va == serialize_cbor v `Seq.append` suff /\
        data_item_wf deterministically_encoded_cbor_map_key_order v == true
    ) ==>
    t v == false

let read_deterministically_encoded_cbor_with_typ_error_postcond_intro_typ_fail
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: raw_data_item)
  (rem: Seq.seq U8.t)
: Lemma
    (requires (
        read_deterministically_encoded_cbor_success_postcond va c v rem /\
        t v == false
    ))
    (ensures (
        read_deterministically_encoded_cbor_with_typ_error_postcond t va
    ))
= serialize_cbor_with_test_correct v rem (fun v' rem' -> data_item_wf deterministically_encoded_cbor_map_key_order v' == true /\ t v' == true)

let read_deterministically_encoded_cbor_with_typ_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError ->
    A.pts_to a #p va ** pure (read_deterministically_encoded_cbor_with_typ_error_postcond t va)
  | ParseSuccess c ->
    exists_ (fun v -> exists_ (fun rem ->
        raw_data_item_match full_perm c.read_cbor_payload v **
        A.pts_to c.read_cbor_remainder #p rem **
        ((raw_data_item_match full_perm c.read_cbor_payload v ** A.pts_to c.read_cbor_remainder #p rem) @==>
        A.pts_to a #p va) **
        pure (read_deterministically_encoded_cbor_with_typ_success_postcond t va c v rem)
    ))

module SZ = FStar.SizeT

inline_for_extraction noextract
```pulse
fn read_deterministically_encoded_cbor_with_typ
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
ensures read_deterministically_encoded_cbor_with_typ_post t a p va res
{
    let res = read_deterministically_encoded_cbor a sz;
    if (ParseSuccess? res) {
        let sres = ParseSuccess?._0 res;
        rewrite (read_deterministically_encoded_cbor_post a p va res) as (read_deterministically_encoded_cbor_success_post a p va sres);
        unfold (read_deterministically_encoded_cbor_success_post a p va sres);
        let test = eval_impl_typ ft sres.read_cbor_payload;
        if (test) {
            fold (read_deterministically_encoded_cbor_with_typ_post t a p va (ParseSuccess sres));
            res
        } else {
            with v . assert (raw_data_item_match full_perm sres.read_cbor_payload v);
            with vrem . assert (A.pts_to sres.read_cbor_remainder #p vrem);
            read_deterministically_encoded_cbor_with_typ_error_postcond_intro_typ_fail t va sres v vrem;
            elim_stick0 ()
                #(raw_data_item_match full_perm sres.read_cbor_payload v ** A.pts_to sres.read_cbor_remainder #p vrem);
            fold (read_deterministically_encoded_cbor_with_typ_post t a p va ParseError);
            ParseError
        }
    } else {
        rewrite (read_deterministically_encoded_cbor_post a p va res) as (read_deterministically_encoded_cbor_error_post a p va);
        unfold (read_deterministically_encoded_cbor_error_post a p va);
        fold (read_deterministically_encoded_cbor_with_typ_post t a p va ParseError);
        res
    }
}
```

let cbor_map_get_with_typ_post
  (t: typ)
  (p: perm)
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound ->
    raw_data_item_match p map vmap ** pure (
        Map? vmap /\
        begin match list_ghost_assoc vkey (Map?.v vmap) with
        | None -> True
        | Some v -> t v == false
        end
    )
  | Found value ->
    exists_ (fun vvalue ->
        raw_data_item_match p value vvalue **
        (raw_data_item_match p value vvalue @==> raw_data_item_match p map vmap) **
        pure (
        Map? vmap /\
        list_ghost_assoc vkey (Map?.v vmap) == Some vvalue /\
        t vvalue == true
    ))

let cbor_map_get_post_eq_found
  (p: perm)
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (fres: cbor)
: Lemma
  (requires (res == Found fres))
  (ensures (
    cbor_map_get_post p vkey vmap map res ==
        cbor_map_get_post_found p vkey vmap map fres
  ))
= ()

```pulse
ghost
fn manurewrite
    (pre post: vprop)
requires
    pre ** pure (pre == post)
ensures
    post
{
    rewrite pre as post
}

```

```pulse
ghost
fn cbor_map_get_found_elim
  (p: perm)
  (vkey: Ghost.erased raw_data_item)
  (vmap: Ghost.erased raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (fres: cbor)
requires
    cbor_map_get_post p vkey vmap map res **
    pure (res == Found fres)
ensures
    cbor_map_get_post_found p vkey vmap map fres
{
    manurewrite (cbor_map_get_post p vkey vmap map res) (cbor_map_get_post_found p vkey vmap map fres)
    // rewrite ... as ... fails: WHY WHY WHY??
}
```

inline_for_extraction noextract
```pulse
fn cbor_map_get_with_typ
  (#t: typ)
  (ft: impl_typ t)
  (key: cbor)
  (map: cbor)
  (#pkey: perm)
  (#vkey: Ghost.erased raw_data_item)
  (#pmap: perm)
  (#vmap: Ghost.erased raw_data_item)
requires
    (raw_data_item_match pkey key vkey ** raw_data_item_match pmap map vmap ** pure (
      Map? vmap /\
      (~ (Tagged? vkey \/ Array? vkey \/ Map? vkey))
    ))
returns res: cbor_map_get_t
ensures
    (raw_data_item_match pkey key vkey ** cbor_map_get_with_typ_post t pmap vkey vmap map res ** pure (
      Map? vmap /\
      Found? res == begin match list_ghost_assoc (Ghost.reveal vkey) (Map?.v vmap) with
      | None -> false
      | Some v -> t v
      end
    ))
{
    let res = cbor_map_get key map;
    if (Found? res) {
        let fres = Found?._0 res;
        manurewrite (cbor_map_get_post pmap vkey vmap map res) (cbor_map_get_post_found pmap vkey vmap map fres);
        unfold (cbor_map_get_post_found pmap vkey vmap map fres);
        let test = eval_impl_typ ft fres;
        if (test) {
            fold (cbor_map_get_with_typ_post t pmap vkey vmap map (Found fres));
            res
        } else {
            elim_stick0 ();
            fold (cbor_map_get_with_typ_post t pmap vkey vmap map NotFound);
            NotFound
        }
    } else {
        rewrite (cbor_map_get_post pmap vkey vmap map res) as (cbor_map_get_post_not_found pmap vkey vmap map);
        unfold (cbor_map_get_post_not_found pmap vkey vmap map);
        fold (cbor_map_get_with_typ_post t pmap vkey vmap map NotFound);
        res
    }
}
```
