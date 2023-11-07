module CBOR.Pulse
include CBOR.Spec.Constants
include CBOR.Pulse.Extern
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Cbor = CBOR.Spec
module A = Pulse.Lib.Array
module SZ = FStar.SizeT

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

assume Fits_u64 : squash (SZ.fits_u64)

```pulse
fn rec cbor_is_equal
  (a1: cbor)
  (a2: cbor)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased Cbor.raw_data_item)
  (#v2: Ghost.erased Cbor.raw_data_item)
requires
    (raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2)
returns res: bool
ensures
    (raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2 ** pure (
      (res == true <==> v1 == v2)
    ))
{
    let test = cbor_is_equal_aux a1 a2;
    match test {
        CborEqual ->
        {
            true
        }
        CborNotEqual ->
        {
            false
        }
        _ ->
        {
            let ty1 = cbor_get_major_type a1;
            let ty2 = cbor_get_major_type a2;
            if (ty1 <> ty2)
            {
                false
            } else if (ty1 = major_type_uint64 || ty1 = major_type_neg_int64) {
                let i1 = destr_cbor_int64 a1;
                let i2 = destr_cbor_int64 a2;
                (i1.cbor_int_value = i2.cbor_int_value)
            } else if (ty1 = major_type_simple_value) {
                let i1 = destr_cbor_simple_value a1;
                let i2 = destr_cbor_simple_value a2;
                (i1 = i2)
            } else if (ty1 = major_type_byte_string || ty1 = major_type_text_string) {
                let s1 = destr_cbor_string a1;
                let s2 = destr_cbor_string a2;
                if (s1.cbor_string_length <> s2.cbor_string_length) {
                    elim_stick0 ();
                    elim_stick0 ();
                    false
                } else {
                    A.pts_to_len s1.cbor_string_payload;
                    A.pts_to_len s2.cbor_string_payload;
                    let test = A.compare (SZ.uint64_to_sizet s1.cbor_string_length) s1.cbor_string_payload s2.cbor_string_payload;
                    elim_stick0 ();
                    elim_stick0 ();
                    test
                }
            } else if (ty1 = major_type_array) {
                let len1 = cbor_array_length a1;
                let len2 = cbor_array_length a2;
                if (len1 <> len2) {
                    false
                } else {
                    let i10 = cbor_array_iterator_init a1;
                    let i20 = cbor_array_iterator_init a2;
                    let done0 = cbor_array_iterator_is_done i10;
                    let mut pi1 = i10;
                    let mut pi2 = i20;
                    let mut pdone = done0;
                    let mut pres = true;
                    while (
                        let done = !pdone;
                        let res = !pres;
                        (res && not done)
                    )
                    invariant cont . exists i1 i2 done res l1 l2 .
                        pts_to pi1 i1 ** pts_to pi2 i2 ** pts_to pdone done ** pts_to pres res **
                        cbor_array_iterator_match p1 i1 l1 **
                        cbor_array_iterator_match p2 i2 l2 **
                        `@(cbor_array_iterator_match p1 i1 l1 @==> raw_data_item_match p1 a1 v1) **
                        `@(cbor_array_iterator_match p2 i2 l2 @==> raw_data_item_match p2 a2 v2) **
                        pure (
                            List.Tot.length l1 == List.Tot.length l2 /\
                            (Ghost.reveal (v1 == v2) <==> (res == true /\ l1 == l2)) /\
                            (res == true ==> done == Nil? l1) /\
                            cont == (Cons? l1 && res)
                        )
                    {
                        let x1 = cbor_array_iterator_next pi1;
                        with v1' . assert (raw_data_item_match p1 x1 v1');
                        let x2 = cbor_array_iterator_next pi2;
                        with v2' . assert (raw_data_item_match p2 x2 v2');
                        let test = perform (fun _ -> cbor_is_equal x1 x2 #p1 #p2 #v1' #v2');
                        with gi1' l1' . assert (pts_to pi1 gi1' ** cbor_array_iterator_match p1 gi1' l1');
                        with gi2' l2' . assert (pts_to pi2 gi2' ** cbor_array_iterator_match p2 gi2' l2');
                        stick_consume_l ()
                            #(raw_data_item_match p1 x1 v1')
                            #(cbor_array_iterator_match p1 gi1' l1');
                        stick_consume_l ()
                            #(raw_data_item_match p2 x2 v2')
                            #(cbor_array_iterator_match p2 gi2' l2');
                        stick_trans ()
                            #(cbor_array_iterator_match p1 gi1' l1');
                        stick_trans ()
                            #(cbor_array_iterator_match p2 gi2' l2');
                        if (test) {
                            let i1 = !pi1;
                            rewrite each gi1' as i1;
                            let done = cbor_array_iterator_is_done i1;
                            pdone := done
                        } else {
                            pres := false
                        }
                    };
                    elim_stick0 ();
                    elim_stick0 ();
                    !pres
                }
            } else if (ty1 = major_type_tagged) {
                let tg1 = destr_cbor_tagged a1;
                let tg2 = destr_cbor_tagged a2;
                if (tg1.cbor_tagged_tag <> tg2.cbor_tagged_tag) {
                    elim_stick0 ();
                    elim_stick0 ();
                    false
                } else {
                    with v1' . assert (raw_data_item_match p1 tg1.cbor_tagged_payload v1');
                    with v2' . assert (raw_data_item_match p2 tg2.cbor_tagged_payload v2');
                    let test = perform (fun _ -> cbor_is_equal tg1.cbor_tagged_payload tg2.cbor_tagged_payload #p1 #p2 #v1' #v2');
                    elim_stick0 ();
                    elim_stick0 ();
                    test
                }
            } else if (ty1 = major_type_map) {
                let len1 = cbor_map_length a1;
                let len2 = cbor_map_length a2;
                if (len1 <> len2) {
                    false
                } else {
                    let i10 = cbor_map_iterator_init a1;
                    let i20 = cbor_map_iterator_init a2;
                    let done0 = cbor_map_iterator_is_done i10;
                    let mut pi1 = i10;
                    let mut pi2 = i20;
                    let mut pdone = done0;
                    let mut pres = true;
                    while (
                        let done = !pdone;
                        let res = !pres;
                        (res && not done)
                    )
                    invariant cont . exists i1 i2 done res l1 l2 .
                        pts_to pi1 i1 ** pts_to pi2 i2 ** pts_to pdone done ** pts_to pres res **
                        cbor_map_iterator_match p1 i1 l1 **
                        cbor_map_iterator_match p2 i2 l2 **
                        `@(cbor_map_iterator_match p1 i1 l1 @==> raw_data_item_match p1 a1 v1) **
                        `@(cbor_map_iterator_match p2 i2 l2 @==> raw_data_item_match p2 a2 v2) **
                        pure (
                            List.Tot.length l1 == List.Tot.length l2 /\
                            (Ghost.reveal (v1 == v2) <==> (res == true /\ l1 == l2)) /\
                            (res == true ==> done == Nil? l1) /\
                            cont == (Cons? l1 && res)
                        )
                    {
                        let x1 = cbor_map_iterator_next pi1;
                        with v1' . assert (raw_data_item_map_entry_match p1 x1 v1');
                        with gi1' l1' . assert (pts_to pi1 gi1' ** cbor_map_iterator_match p1 gi1' l1');
                        stick_trans ()
                            #(raw_data_item_map_entry_match p1 x1 v1' ** cbor_map_iterator_match p1 gi1' l1');
                        let x2 = cbor_map_iterator_next pi2;
                        with v2' . assert (raw_data_item_map_entry_match p2 x2 v2');
                        with gi2' l2' . assert (pts_to pi2 gi2' ** cbor_map_iterator_match p2 gi2' l2');
                        stick_trans ()
                            #(raw_data_item_map_entry_match p2 x2 v2' ** cbor_map_iterator_match p2 gi2' l2');
                        unfold (raw_data_item_map_entry_match p1 x1 v1');
                        unfold (raw_data_item_map_entry_match p2 x2 v2');
                        let test = perform (fun _ -> cbor_is_equal (cbor_map_entry_key x1) (cbor_map_entry_key x2) #p1 #p2 #(fstp v1') #(fstp v2'));
                        if test ensures exists res done . // FIXME: HOW HOW HOW can I frame some things out?
                            pts_to pi1 gi1' ** pts_to pi2 gi2' ** pts_to pdone done **
                            raw_data_item_match p1 (cbor_map_entry_key x1) (fstp v1') **
                            raw_data_item_match p2 (cbor_map_entry_key x2) (fstp v2') **
                            raw_data_item_match p1 (cbor_map_entry_value x1) (sndp v1') **
                            raw_data_item_match p2 (cbor_map_entry_value x2) (sndp v2') **
                            cbor_map_iterator_match p1 gi1' l1' **
                            cbor_map_iterator_match p2 gi2' l2' **
                            `@((raw_data_item_map_entry_match p1 x1 v1' ** cbor_map_iterator_match p1 gi1' l1') @==> raw_data_item_match p1 a1 v1) **
                            `@((raw_data_item_map_entry_match p2 x2 v2' ** cbor_map_iterator_match p2 gi2' l2') @==> raw_data_item_match p2 a2 v2) **
                            pts_to pres res ** pure (res == true <==> v1' == v2')
                        {
                            let test = perform (fun _ -> cbor_is_equal (cbor_map_entry_value x1) (cbor_map_entry_value x2) #p1 #p2 #(sndp v1') #(sndp v2'));
                            pres := test;
                        } else {
                            pres := false;
                        };
                        fold (raw_data_item_map_entry_match p1 x1 v1');
                        fold (raw_data_item_map_entry_match p2 x2 v2');
                        stick_consume_l ()
                            #(raw_data_item_map_entry_match p1 x1 v1')
                            #(cbor_map_iterator_match p1 gi1' l1');
                        stick_consume_l ()
                            #(raw_data_item_map_entry_match p2 x2 v2')
                            #(cbor_map_iterator_match p2 gi2' l2');
                        let res = !pres;
                        if (res) {
                            let i1 = !pi1;
                            rewrite each gi1' as i1;
                            let done = cbor_map_iterator_is_done i1;
                            pdone := done
                        }
                    };
                    elim_stick0 ();
                    elim_stick0 ();
                    !pres
                }
            } else {
                // unreachable
                let unused : squash False = ();
                false
            }
        }
    }
}

```

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
      Cbor.Map? vmap
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
