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
    (#v: Ghost.erased raw_data_item) ->
    stt bool
        (raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) b
        ))
        (fun res -> raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) b /\
            res == t v
        ))

inline_for_extraction noextract
let eval_impl_typ
    (#b: Ghost.erased (option raw_data_item))
    (#t: bounded_typ_gen b)
    (f: impl_typ t)
    (c: cbor)
    (#v: Ghost.erased raw_data_item)
:   stt bool
        (raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
        (fun res -> raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
            res == t v
        ))
= f c #v

inline_for_extraction noextract
```pulse
fn impl_coerce_to_bounded_typ'
    (b: Ghost.erased (option raw_data_item))
    (#t: typ)
    (f: impl_typ t)
    (c: cbor)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
returns res: bool
ensures
        (raw_data_item_match c v ** pure (
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
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match c v ** pure (
            opt_precedes (Ghost.reveal v) (Ghost.reveal b)
        ))
returns res: bool
ensures
        (raw_data_item_match c v ** pure (
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

inline_for_extraction
let impl_t_choice
    (#b: Ghost.erased (option raw_data_item))
    (#t1 #t2: bounded_typ_gen b)
    (f1: impl_typ t1)
    (f2: impl_typ t2)
: Tot (impl_typ (t_choice t1 t2))
= impl_t_choice' f1 f2

inline_for_extraction noextract
let impl_array_group3
    (#b: option raw_data_item)
    (g: array_group3 b)
: Tot Type
=
    (pi: R.ref cbor_array_iterator_t) ->
    (#i: Ghost.erased cbor_array_iterator_t) ->
    (#l: Ghost.erased (list raw_data_item)) ->
    stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match i l **
            pure (opt_precedes (Ghost.reveal l) b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
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
    (#i: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
:   stt bool
        (R.pts_to pi i **
            cbor_array_iterator_match i l **
            pure (opt_precedes (Ghost.reveal l) b)
        )
        (fun res -> exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
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
    (i: cbor_array_iterator_t)
    (l: list raw_data_item)
    (res: bool)
    (i': cbor_array_iterator_t)
    (l': list raw_data_item)
requires
    (
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            `@(cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
            pure (
                opt_precedes (Ghost.reveal l) b /\
                res == Some? (g l) /\
                (res == true ==> Some?.v (g l) == l')
            )
    )
ensures
        (exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match i l) **
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
fn impl_array_group3_item'
    (#b: Ghost.erased (option raw_data_item))
    (#ty: bounded_typ_gen b)
    (fty: impl_typ ty)
    (pi: R.ref cbor_array_iterator_t)
    (#gi: Ghost.erased cbor_array_iterator_t)
    (#l: Ghost.erased (list raw_data_item))
requires
        (R.pts_to pi gi **
            cbor_array_iterator_match gi l **
            pure (opt_precedes (Ghost.reveal l) (Ghost.reveal b))
        )
returns res: bool
ensures
        (exists_ (fun i' -> exists_ (fun l' ->
            R.pts_to pi i' **
            cbor_array_iterator_match i' l' **
            (cbor_array_iterator_match i' l' @==> cbor_array_iterator_match gi l) **
            pure (
                opt_precedes (Ghost.reveal l) (Ghost.reveal b) /\
                res == Some? (array_group3_item ty l) /\
                (res == true ==> Some?.v (array_group3_item ty l) == l')
            )
        )))
{
    let i = !pi;
    rewrite (cbor_array_iterator_match gi l) as (cbor_array_iterator_match i l);
    let is_done = cbor_array_iterator_is_done i;
    rewrite (cbor_array_iterator_match i l) as (cbor_array_iterator_match gi l);
    if (is_done) {
        stick_refl0 (cbor_array_iterator_match gi l);
        intro_impl_array_group3_post (array_group3_item ty) pi gi l false gi l; // FIXME: WHY WHY WHY? and also WHY WHY WHY here and not in the other "false" case below?
        false
    } else {
        let c = cbor_array_iterator_next pi #l #gi; // FIXME: WHY WHY WHY those explicit arguments?
        with gc i' l' . assert (
            raw_data_item_match c gc **
            cbor_array_iterator_match i' l' **
            `@((raw_data_item_match c gc ** cbor_array_iterator_match i' l') @==> cbor_array_iterator_match gi l)
        ); // this is needed for the explicit arguments to split_consume_l below
        let test = eval_impl_typ fty c;
        if (test) {
            stick_consume_l ()
                #(raw_data_item_match c gc)
                #(cbor_array_iterator_match i' l')
                #(cbor_array_iterator_match gi l) // FIXME: WHY WHY WHY those explicit arguments? (for which the with above is needed)
            ;
            true
        } else {
            elim_stick0 ()
                #(raw_data_item_match c gc ** cbor_array_iterator_match i' l')
                #(cbor_array_iterator_match gi l); // FIXME: WHY WHY WHY those explicit arguments?
            pi := i;
            rewrite (R.pts_to pi i) as (R.pts_to pi gi);
            stick_refl0 (cbor_array_iterator_match gi l);
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
    (#v: Ghost.erased raw_data_item)
requires
    raw_data_item_match c v **
    pure (opt_precedes (Ghost.reveal v) (Ghost.reveal b))
returns res: bool
ensures
    raw_data_item_match c v **
    pure (
        opt_precedes (Ghost.reveal v) (Ghost.reveal b) /\
        res == t_array3 g v
    )
{
    let ty = cbor_get_major_type c;
    if (ty = major_type_array) {
        let i = cbor_array_iterator_init c;
        with l . assert (cbor_array_iterator_match i l);
        rewrite (cbor_array_iterator_match i l) as (cbor_array_iterator_match (Ghost.reveal (Ghost.hide i)) l);
        let mut pi = i;
        let b_success = eval_impl_array_group3 ig pi;
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

let read_deterministically_encoded_cbor_with_typ_success_post
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
    pure (read_deterministically_encoded_cbor_with_typ_success_postcond t va c v rem)
  ))

noextract
let read_deterministically_encoded_cbor_with_typ_error_postcond
  (t: typ)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v .
    (serialize_cbor v == Seq.slice va 0 (min (Seq.length (serialize_cbor v)) (Seq.length va)) /\
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

let read_deterministically_encoded_cbor_with_typ_error_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a #p va ** pure (read_deterministically_encoded_cbor_with_typ_error_postcond t va)

let read_deterministically_encoded_cbor_with_typ_post
  (t: typ)
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_deterministically_encoded_cbor_with_typ_error_post t a p va
  | ParseSuccess c -> read_deterministically_encoded_cbor_with_typ_success_post t a p va c

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
            fold (read_deterministically_encoded_cbor_with_typ_success_post t a p va sres);
            rewrite (read_deterministically_encoded_cbor_with_typ_success_post t a p va sres) as (read_deterministically_encoded_cbor_with_typ_post t a p va res);
            res
        } else {
            with v . assert (raw_data_item_match sres.read_cbor_payload v);
            with vrem . assert (A.pts_to sres.read_cbor_remainder #p vrem);
            read_deterministically_encoded_cbor_with_typ_error_postcond_intro_typ_fail t va sres v vrem;
            elim_stick0 ()
                #(raw_data_item_match sres.read_cbor_payload v ** A.pts_to sres.read_cbor_remainder #p vrem);
            fold (read_deterministically_encoded_cbor_with_typ_error_post t a p va);
            rewrite (read_deterministically_encoded_cbor_with_typ_error_post t a p va) as (read_deterministically_encoded_cbor_with_typ_post t a p va ParseError);
            ParseError
        }
    } else {
        rewrite (read_deterministically_encoded_cbor_post a p va res) as (read_deterministically_encoded_cbor_error_post a p va);
        unfold (read_deterministically_encoded_cbor_error_post a p va);
        fold (read_deterministically_encoded_cbor_with_typ_error_post t a p va);
        rewrite (read_deterministically_encoded_cbor_with_typ_error_post t a p va) as (read_deterministically_encoded_cbor_with_typ_post t a p va res);
        res
    }
}
```


let cbor_map_get_with_typ_post_not_found
  (t: typ)
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
: Tot vprop
= raw_data_item_match map vmap ** pure (
    Map? vmap /\
    begin match list_ghost_assoc vkey (Map?.v vmap) with
    | None -> True
    | Some v -> t v == false
    end
  )

let cbor_map_get_with_typ_post_found
  (t: typ)
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists_ (fun vvalue ->
    raw_data_item_match value vvalue **
    (raw_data_item_match value vvalue @==> raw_data_item_match map vmap) **
    pure (
      Map? vmap /\
      list_ghost_assoc vkey (Map?.v vmap) == Some vvalue /\
      t vvalue == true
  ))

let cbor_map_get_with_typ_post
  (t: typ)
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_with_typ_post_not_found t vkey vmap map
  | Found value -> cbor_map_get_with_typ_post_found t vkey vmap map value

let cbor_map_get_post_eq_found
  (vkey: raw_data_item)
  (vmap: raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (fres: cbor)
: Lemma
  (requires (res == Found fres))
  (ensures (
    cbor_map_get_post vkey vmap map res ==
        cbor_map_get_post_found vkey vmap map fres
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
  (vkey: Ghost.erased raw_data_item)
  (vmap: Ghost.erased raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
  (fres: cbor)
requires
    cbor_map_get_post vkey vmap map res **
    pure (res == Found fres)
ensures
    cbor_map_get_post_found vkey vmap map fres
{
    manurewrite (cbor_map_get_post vkey vmap map res) (cbor_map_get_post_found vkey vmap map fres)
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
  (#vkey: Ghost.erased raw_data_item)
  (#vmap: Ghost.erased raw_data_item)
requires
    (raw_data_item_match key vkey ** raw_data_item_match map vmap ** pure (
      Map? vmap /\
      (~ (Tagged? vkey \/ Array? vkey \/ Map? vkey))
    ))
returns res: cbor_map_get_t
ensures
    (raw_data_item_match key vkey ** cbor_map_get_with_typ_post t vkey vmap map res ** pure (
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
        manurewrite (cbor_map_get_post vkey vmap map res) (cbor_map_get_post_found vkey vmap map fres);
        unfold (cbor_map_get_post_found vkey vmap map fres);
        let test = eval_impl_typ ft fres;
        if (test) {
            fold (cbor_map_get_with_typ_post_found t vkey vmap map fres);
            manurewrite (cbor_map_get_with_typ_post_found t vkey vmap map fres) (cbor_map_get_with_typ_post t vkey vmap map res);
            res
        } else {
            elim_stick0 ();
            fold (cbor_map_get_with_typ_post_not_found t vkey vmap map);
            rewrite (cbor_map_get_with_typ_post_not_found t vkey vmap map) as (cbor_map_get_with_typ_post t vkey vmap map NotFound);
            NotFound
        }
    } else {
        rewrite (cbor_map_get_post vkey vmap map res) as (cbor_map_get_post_not_found vkey vmap map);
        unfold (cbor_map_get_post_not_found vkey vmap map);
        fold (cbor_map_get_with_typ_post_not_found t vkey vmap map);
        rewrite (cbor_map_get_with_typ_post_not_found t vkey vmap map) as (cbor_map_get_with_typ_post t vkey vmap map res);
        res
    }
}
```
