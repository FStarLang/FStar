module CDDL.Spec
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Concise Data Definition Language (RFC 8610)

noextract
let opt_precedes
  (#t1 #t2: Type)
  (x1: t1)
  (x2: option t2)
: Tot prop
= match x2 with
  | None -> True
  | Some x2 -> x1 << x2

[@@noextract_to "krml"]
let bounded_typ_gen (e: option Cbor.raw_data_item) = (e': Cbor.raw_data_item { opt_precedes e' e }) -> GTot bool  // GTot needed because of the .cbor control (staged serialization)

[@@noextract_to "krml"]
let typ = bounded_typ_gen None

[@@noextract_to "krml"]
let bounded_typ (e: Cbor.raw_data_item) = bounded_typ_gen (Some e)

let coerce_to_bounded_typ
  (b: option Cbor.raw_data_item)
  (t: typ)
: Tot (bounded_typ_gen b)
= t

noextract
let typ_equiv
  (#b: option Cbor.raw_data_item)
  (t1 t2: bounded_typ_gen b)
: Tot prop
= forall x . t1 x == t2 x

let t_choice (#b: option Cbor.raw_data_item) (t1 t2: bounded_typ_gen b) : bounded_typ_gen b = (fun x -> t1 x || t2 x)

let t_choice_equiv
  #b
  (t1 t1' t2 t2' : bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t1' /\ t2 `typ_equiv` t2'))
  (ensures ((t1 `t_choice` t2) `typ_equiv` (t1' `t_choice` t2')))
= ()
// etc.

let t_choice_simpl
  #b
  (t: bounded_typ_gen b)
: Lemma
  ((t `t_choice` t) `typ_equiv` t)
= ()

let t_always_false : typ = (fun _ -> false)

let t_literal (i: Cbor.raw_data_item) : typ =
  (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x == i))

// Appendix D
let any : typ = (fun _ -> true)

let uint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.major_type_uint64)
let nint : typ = (fun x -> Cbor.Int64? x && Cbor.Int64?.typ x = Cbor.major_type_neg_int64)
let t_int : typ = uint `t_choice` nint

let bstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.major_type_byte_string)
let bytes = bstr
let tstr : typ = (fun x -> Cbor.String? x && Cbor.String?.typ x = Cbor.major_type_text_string)
let text = tstr

[@@CMacro]
let simple_value_false : Cbor.simple_value = 20uy
[@@CMacro]
let simple_value_true : Cbor.simple_value = 21uy
[@@CMacro]
let simple_value_nil : Cbor.simple_value = 22uy
[@@CMacro]
let simple_value_undefined : Cbor.simple_value = 23uy

let t_simple_value_literal (s: Cbor.simple_value) : typ =
  t_literal (Cbor.Simple s)

let t_false : typ = t_simple_value_literal simple_value_false
let t_true : typ = t_simple_value_literal simple_value_true
let t_bool : typ = t_choice t_false t_true
let t_nil : typ = t_simple_value_literal simple_value_nil
let t_null : typ = t_nil
let t_undefined : typ = t_simple_value_literal simple_value_undefined

let t_uint_literal (v: U64.t) : typ =
  t_literal (Cbor.Int64 Cbor.major_type_uint64 v)

// Section 2.1: Groups 

// Groups in array context (Section 3.4)
// General semantics, which would imply backtracking

[@@erasable; noextract_to "krml"]
let array_group1 = ((list Cbor.raw_data_item -> GTot bool) -> list Cbor.raw_data_item -> GTot bool)
let array_group1_empty : array_group1 = fun k -> k
let array_group1_concat (a1 a2: array_group1) : array_group1 = fun k -> a1 (a2 k)
let array_group1_choice (a1 a2: array_group1) : array_group1 = fun k l -> a1 k l || a2 k l

let rec array_group1_zero_or_more' (a: array_group1) (k: (list Cbor.raw_data_item -> GTot bool)) (l: list Cbor.raw_data_item) : GTot bool (decreases (List.Tot.length l)) =
  k l ||
  a (fun l' -> if List.Tot.length l' >= List.Tot.length l then false else array_group1_zero_or_more' a k l') l

let array_group1_zero_or_more : array_group1 -> array_group1 = array_group1_zero_or_more'

let array_group1_item (t: typ) : array_group1 = fun k l -> match l with
  | [] -> false
  | a :: q -> t a && k q

let t_array1 (a: array_group1) : typ = fun x ->
  Cbor.Array? x &&
  a Nil? (Cbor.Array?.v x) 

[@@noextract_to "krml"]
let nat_up_to (n: nat) : eqtype = (i: nat { i <= n })

[@@noextract_to "krml"]
let array_group2 = ((l: Seq.seq Cbor.raw_data_item) -> (i: nat_up_to (Seq.length l)) -> list (nat_up_to (Seq.length l)))
[@@noextract_to "krml"]
let array_group2_empty : array_group2 = (fun _ i -> [i])
[@@noextract_to "krml"]
let array_group2_concat (a1 a2: array_group2) : array_group2 =
  (fun l i1 ->
    let res1 = a1 l i1 in
    List.Tot.concatMap (fun (i2: nat_up_to (Seq.length l)) -> a2 l i2) res1
  )

[@@noextract_to "krml"]
let array_group2_choice (a1 a2: array_group2) : array_group2 =
  fun l i -> a1 l i `List.Tot.append` a2 l i

[@@noextract_to "krml"]
let rec array_group2_zero_or_more' (a: array_group2) (l: Seq.seq Cbor.raw_data_item) (i: nat_up_to (Seq.length l)) : Tot (list (nat_up_to (Seq.length l))) (decreases (Seq.length l - i)) =
  i :: begin
    let r1 = a l i in
    List.Tot.concatMap (fun (i2: nat_up_to (Seq.length l)) ->
      if i2 <= i
      then []
      else array_group2_zero_or_more' a l i2
    )
    r1
  end

(*
[@@noextract_to "krml"]
let array_group2_item (t: typ) : array_group2 = fun l i ->
  if i = Seq.length l then [] else
  if t (Seq.index l i) then [i + 1] else
  []
*)

[@@noextract_to "krml"]
let t_array2 (a: array_group2) : typ = fun x ->
  Cbor.Array? x &&
  begin let l = Cbor.Array?.v x in
    List.Tot.length l `List.Tot.mem` a (Seq.seq_of_list l) 0
  end

// Greedy semantics (Appendix A?)

let list_is_suffix_of
  (#t: Type)
  (small large: list t)
: Tot prop
= exists prefix . large == prefix `List.Tot.append` small

let list_is_suffix_of_refl
  (#t: Type)
  (l: list t)
: Lemma
  (l `list_is_suffix_of` l)
  [SMTPat (l `list_is_suffix_of` l)]
= assert (l == [] `List.Tot.append` l)

let rec list_nil_precedes
  (#t: Type)
  (l: list t)
: Lemma
  (Nil #t == l \/ Nil #t << l)
= match l with
  | [] -> ()
  | a :: q -> list_nil_precedes q

let rec list_is_suffix_of_precedes
  (#t0 #t: Type)
  (v0: t0)
  (small large: list t)
: Lemma
  (requires (
    large << v0 /\
    small `list_is_suffix_of` large
  ))
  (ensures (
    small << v0
  ))
  (decreases (List.Tot.length large))
  [SMTPat [small << v0]; SMTPat [small `list_is_suffix_of` large]]
= if Nil? small
  then list_nil_precedes large
  else begin
    let prefix = FStar.IndefiniteDescription.indefinite_description_ghost (list t) (fun prefix -> large == prefix `List.Tot.append` small) in
    List.Tot.append_length prefix small;
    if List.Tot.length small = List.Tot.length large
    then ()
    else list_is_suffix_of_precedes v0 small (List.Tot.tl large)
  end

[@@erasable; noextract_to "krml"]
let array_group3 (bound: option Cbor.raw_data_item) = (l: list Cbor.raw_data_item { opt_precedes l bound }) -> Ghost (option (list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with
  | None -> True
  | Some l' -> opt_precedes l' bound
  ))

noextract
let array_group3_equiv
  #b
  (g1 g2: array_group3 b)
: Tot prop
= forall l . g1 l == g2 l

let array_group3_always_false #b : array_group3 b = fun _ -> None
let array_group3_empty #b : array_group3 b = fun x -> Some x
let array_group3_concat #b (a1 a3: array_group3 b) : array_group3 b =
  (fun l ->
    match a1 l with
    | None -> None
    | Some l3 -> a3 l3
  )

let array_group3_concat_equiv
  #b
  (a1 a1' a2 a2' : array_group3 b)
: Lemma
  (requires ((a1 `array_group3_equiv` a1') /\ (a2 `array_group3_equiv` a2')))
  (ensures ((a1 `array_group3_concat` a2) `array_group3_equiv` (a1' `array_group3_concat` a2')))
= ()

let array_group3_choice #b (a1 a3: array_group3 b) : array_group3 b =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let rec array_group3_zero_or_more' #b (a: array_group3 b) (l: list Cbor.raw_data_item { opt_precedes l b }) : Ghost (option (list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with None -> True | Some l' -> opt_precedes l' b))
  (decreases (List.Tot.length l))
=
  match a l with
  | None -> Some l
  | Some l' ->
    if List.Tot.length l' >= List.Tot.length l
    then Some l
    else array_group3_zero_or_more' a l'

let array_group3_zero_or_more #b : array_group3 b -> array_group3 b = array_group3_zero_or_more'

let array_group3_one_or_more #b (a: array_group3 b) : array_group3 b =
  a `array_group3_concat` array_group3_zero_or_more a

let array_group3_zero_or_one #b (a: array_group3 b) : Tot (array_group3 b) =
  a `array_group3_choice` array_group3_empty

let array_group3_item (#b: option Cbor.raw_data_item) (t: bounded_typ_gen b) : array_group3 b = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some q else None

let array_group3_item_equiv
  #b
  (t1 t2: bounded_typ_gen b)
: Lemma
  (requires (t1 `typ_equiv` t2))
  (ensures (array_group3_item t1 `array_group3_equiv` array_group3_item t2))
= ()

let match_array_group3 (#b: option Cbor.raw_data_item) (a: array_group3 b)
  (l: list Cbor.raw_data_item {opt_precedes l b})
: GTot bool
= match a l with
  | Some l' -> Nil? l'
  | _ -> false

let t_array3 (#b: option Cbor.raw_data_item) (a: array_group3 b) : bounded_typ_gen b = fun x ->
  Cbor.Array? x &&
  match_array_group3 a (Cbor.Array?.v x)

let t_array3_equiv
  #b
  (a1 a2: array_group3 b)
: Lemma
  (requires (array_group3_equiv a1 a2))
  (ensures (typ_equiv (t_array3 a1) (t_array3 a2)))
= ()

// Recursive type (needed by COSE Section 5.1 "Recipient")

// Inspiring from Barthe et al., Type-Based Termination with Sized
// Products (CSL 2008): we allow recursion only at the level of
// destructors. In other words, instead of having a generic recursion
// combinator, we provide a recursion-enabled version only for each
// destructor combinator. We need to annotate it with a bound b (akin
// to the "size" annotation in a sized type.)

let rec t_array3_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> array_group3 (Some b)))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
=
  Cbor.Array? x &&
  match_array_group3 (phi x (t_array3_rec phi)) (Cbor.Array?.v x)

// Groups in map context (Section 3.5)

[@@erasable]
noeq
type map_group_entry (b: option Cbor.raw_data_item) = | MapGroupEntry: (fst: bounded_typ_gen b) -> (snd: bounded_typ_gen b) -> map_group_entry b

module Pull = FStar.Ghost.Pull

noextract
let opt_map_entry_bounded'
  (b: option Cbor.raw_data_item)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (opt_precedes x b)

let opt_map_entry_bounded
  (b: option Cbor.raw_data_item)
: GTot ((Cbor.raw_data_item & Cbor.raw_data_item) -> bool)
= Pull.pull (opt_map_entry_bounded' b)

let rec opt_precedes_map_for_all_opt_map_entry_bounded
  (b: option Cbor.raw_data_item)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (opt_precedes l b))
  (ensures (List.Tot.for_all (opt_map_entry_bounded b) l))
  [SMTPat (List.Tot.for_all (opt_map_entry_bounded b) l)]
= match l with
  | [] -> ()
  | _ :: q -> opt_precedes_map_for_all_opt_map_entry_bounded b q

let matches_map_group_entry
  (#b: option Cbor.raw_data_item)
  (ge: map_group_entry b)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item) { opt_map_entry_bounded b x == true })
: GTot bool
= ge.fst (fst x) && ge.snd (snd x)

[@@erasable]
noeq
type map_group (b: option Cbor.raw_data_item) = {
  one: list (map_group_entry b);
  zero_or_one: list (map_group_entry b);
  zero_or_more: list (map_group_entry b);
}

let map_group_empty #b : map_group b = {
  one = [];
  zero_or_one = [];
  zero_or_more = [];
}

let cut_map_group_entry_key
  #b
  (key: bounded_typ_gen b)
  (t: bounded_typ_gen b)
  (x: Cbor.raw_data_item { opt_precedes x b })
: GTot bool
= t x && not (key x)

// Section 3.5.4: Cut
let cut_map_group_entry #b (key: bounded_typ_gen b) (ge: map_group_entry b) : map_group_entry b =
  cut_map_group_entry_key key ge.fst `MapGroupEntry` ge.snd

let cut_map_group #b (key: bounded_typ_gen b) (g: map_group b) : map_group b = {
  one = List.Tot.map (cut_map_group_entry key) g.one;
  zero_or_one = List.Tot.map (cut_map_group_entry key) g.zero_or_one;
  zero_or_more = List.Tot.map (cut_map_group_entry key) g.zero_or_more;
}

let maybe_cut_map_group #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  if cut
  then cut_map_group (ge.fst) g
  else g

let map_group_cons_one #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    one = ge :: g.one;
  }

let map_group_cons_zero_or_one #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_one = ge :: g.zero_or_one;
  }

let map_group_cons_zero_or_more #b (ge: map_group_entry b) (cut: bool) (g: map_group b) : map_group b =
  let g = maybe_cut_map_group ge cut g in {
    g with
    zero_or_more = ge :: g.zero_or_more;
}

val matches_map_group
  (#b: option Cbor.raw_data_item)
  (m: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {List.Tot.for_all (opt_map_entry_bounded b) x })
: GTot bool

val matches_map_group_empty
  (b: option Cbor.raw_data_item)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (ensures (matches_map_group (map_group_empty #b) x == Nil? x))
  [SMTPat (matches_map_group (map_group_empty #b) x)]

(* Inclusion and equivalence proofs for map groups. Those are meant as the main proof devices for matches_map_group *)

noextract
let is_sub_map_group_of
  #b
  (small large: map_group b)
: Tot prop
= forall x . matches_map_group small x ==> matches_map_group large x

noextract
let map_group_equiv
  #b
  (mg1 mg2: map_group b)
: Tot prop
= forall x . matches_map_group mg1 x == matches_map_group mg2 x

noextract
let is_sub_typ_of
 #b
  (small large: bounded_typ_gen b)
: Tot prop
= forall (x: Cbor.raw_data_item { opt_precedes x b }) . small x ==> large x

noextract
let is_sub_map_group_entry_of
 #b
  (small large: map_group_entry b)
: Tot prop
= small.fst `is_sub_typ_of` large.fst /\
  small.snd `is_sub_typ_of` large.snd

let map_group_ignore_restricted_entries
  #b
  (mg: map_group b)
: Tot (map_group b)
= {mg with
      one = [];
      zero_or_one = [];
  }

let pull_rel
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (x1: t1)
: GTot ((x2: t2) -> Tot bool)
= Pull.pull (fun x2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (r x1 x2))

let list_ghost_forall_exists_body
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l2: list t2)
: GTot (t1 -> bool)
= Pull.pull (fun x1 -> List.Tot.existsb
    (pull_rel r x1)
    l2
  )

let list_ghost_forall_exists
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (l1: list t1)
  (l2: list t2)
: GTot bool
= List.Tot.for_all
    (list_ghost_forall_exists_body r l2)
    l1

noextract
let matches_map_group_entry'
  (#b: _)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item))
  (y: map_group_entry b)
: Tot prop
= opt_map_entry_bounded b x ==> matches_map_group_entry y x

val matches_map_group_no_restricted
  (#b: _)
  (g: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (
    Nil? g.one /\
    Nil? g.zero_or_one
  ))
  (ensures (
    matches_map_group g x <==> list_ghost_forall_exists matches_map_group_entry' x g.zero_or_more
  ))
  [SMTPat (matches_map_group g x)]

let rec list_ghost_forall2
  (#t1 #t2: Type)
  (f: t1 -> t2 -> GTot prop)
  (l1: list t1)
  (l2: list t2)
: GTot bool
  (decreases l1)
= match l1, l2 with
  | [], [] -> true
  | a1 :: q1, a2 :: q2 -> FStar.StrongExcludedMiddle.strong_excluded_middle (f a1 a2) && list_ghost_forall2 f q1 q2
  | _ -> false

val list_ghost_forall_exists_is_sub_map_group_entry_of_refl
  (#b: _)
  (l: list (map_group_entry b))
: Lemma
  (ensures (list_ghost_forall_exists is_sub_map_group_entry_of l l))
  [SMTPat (list_ghost_forall_exists is_sub_map_group_entry_of l l)]

let map_group_included_zero_or_more
  #b
  (small large: map_group b)
: GTot bool
= list_ghost_forall_exists is_sub_map_group_entry_of small.one large.zero_or_more &&
  list_ghost_forall_exists is_sub_map_group_entry_of small.zero_or_one large.zero_or_more &&
  list_ghost_forall_exists is_sub_map_group_entry_of small.zero_or_more large.zero_or_more &&
  Nil? large.one

val map_group_included_zero_or_more_correct
  (#b: _)
  (small large: map_group b)
: Lemma
  (requires (map_group_included_zero_or_more small large))
  (ensures (is_sub_map_group_of small large))

val map_group_ignore_restricted_entries_sub
  (#b: _)
  (mg: map_group b)
: Lemma
  (requires (
    list_ghost_forall_exists is_sub_map_group_entry_of mg.one mg.zero_or_more /\
    list_ghost_forall_exists is_sub_map_group_entry_of mg.zero_or_one mg.zero_or_more
  ))
  (ensures (
    mg `is_sub_map_group_of` map_group_ignore_restricted_entries mg
  ))

let map_group_ignore_restricted_entries_no_one_equiv
  #b
  (mg: map_group b)
: Lemma
  (requires (
    Nil? mg.one /\
    list_ghost_forall_exists is_sub_map_group_entry_of mg.zero_or_one mg.zero_or_more
  ))
  (ensures (
    map_group_equiv mg (map_group_ignore_restricted_entries mg)
  ))
= map_group_ignore_restricted_entries_sub mg;
  map_group_included_zero_or_more_correct (map_group_ignore_restricted_entries mg) mg

let map_group_included_pointwise
  #b
  (small large: map_group b)
: GTot bool
= list_ghost_forall2 is_sub_map_group_entry_of small.one large.one &&
  list_ghost_forall2 is_sub_map_group_entry_of small.zero_or_one large.zero_or_one &&
  list_ghost_forall2 is_sub_map_group_entry_of small.zero_or_more large.zero_or_more

val map_group_included_pointwise_correct
  (#b: _)
  (small large: map_group b)
: Lemma
  (requires (map_group_included_pointwise small large))
  (ensures (is_sub_map_group_of small large))

let rec list_ghost_forall2_map_l
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (f: t2 -> t1)
  (l: list t2)
: Lemma
  (requires (forall x . r (f x) x))
  (ensures (list_ghost_forall2 r (List.Tot.map f l) l))
= match l with 
  | [] -> ()
  | _ :: q -> list_ghost_forall2_map_l r f q

let rec list_ghost_forall2_map_r
  (#t1 #t2: Type)
  (r: t1 -> t2 -> prop)
  (f: t1 -> t2)
  (l: list t1)
: Lemma
  (requires (forall x . r x (f x)))
  (ensures (list_ghost_forall2 r l (List.Tot.map f l)))
= match l with 
  | [] -> ()
  | _ :: q -> list_ghost_forall2_map_r r f q

let cut_map_group_sub
  #b
  (key: bounded_typ_gen b)
  (mg: map_group b)
: Lemma
  (cut_map_group key mg `is_sub_map_group_of` mg)
= list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.one;
  list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.zero_or_one;
  list_ghost_forall2_map_l is_sub_map_group_entry_of (cut_map_group_entry key) mg.zero_or_more;
  map_group_included_pointwise_correct (cut_map_group key mg) mg

(* Proving matches_map_group for sorted maps and map groups where key constraints specify whole elements *)

let rec list_for_all_filter_invariant
  (#t: Type)
  (p: t -> bool)
  (f: t -> bool)
  (l: list t)
: Lemma
  (requires (List.Tot.for_all p l == true))
  (ensures (List.Tot.for_all p (List.Tot.filter f l) == true))
  [SMTPat (List.Tot.for_all p (List.Tot.filter f l))]
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_filter_invariant p f q

let map_key_neq'
  (#t1 t2: Type)
  (k: t1)
  (x: (t1 & t2))
: GTot bool
= FStar.StrongExcludedMiddle.strong_excluded_middle (~ (fst x == k))

let map_key_neq
  (#t1 t2: Type)
  (k: t1)
: GTot ((t1 & t2) -> bool)
= Pull.pull (map_key_neq' t2 k)

let map_group_entry_for
  #b
  (k: Cbor.raw_data_item)
  (ty: bounded_typ_gen b)
: Tot (map_group_entry b)
= MapGroupEntry (coerce_to_bounded_typ _ (t_literal k)) ty

let rec list_ghost_assoc_for_all
  (#key: Type)
  (#value: Type)
  (p: (key & value) -> bool)
  (k: key)
  (m: list (key & value))
: Lemma
  (requires (List.Tot.for_all p m == true))
  (ensures (match Cbor.list_ghost_assoc k m with
  | None -> True
  | Some y -> p (k, y)
  ))
  (decreases m)
  [SMTPat (List.Tot.for_all p m); SMTPat (Cbor.list_ghost_assoc k m)]
= match m with
  | [] -> ()
  | (k', _) :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then ()
    else list_ghost_assoc_for_all p k m'

let rec list_assoc_none_for_all_map_key_neq
  (k: Cbor.raw_data_item)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Lemma
  (requires (None? (Cbor.list_ghost_assoc k l)))
  (ensures (List.Tot.for_all (map_key_neq _ k) l == true))
= match l with
  | [] -> ()
  | _ :: q -> list_assoc_none_for_all_map_key_neq k q

val matches_map_group_map_group_cons_zero_or_one_no_repeats
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> matches_map_group g x
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))

val matches_map_group_map_group_cons_one_no_repeats
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.no_repeats_p (List.Tot.map fst x)))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b
    end /\
    matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> false
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))

val matches_map_group_map_group_cons_zero_or_one_deterministically_encoded_cbor_map_key_order
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) x))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b /\ List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter (map_key_neq _ k) x)
    end /\
    matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> matches_map_group g x
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
  [SMTPat (matches_map_group (map_group_cons_zero_or_one (map_group_entry_for k ty) true g) x)]

val matches_map_group_map_group_cons_one_deterministically_encoded_cbor_map_key_order
   (#b: _) (k: Cbor.raw_data_item) (ty: bounded_typ_gen b) (g: map_group b)
   (x: list (Cbor.raw_data_item & Cbor.raw_data_item) { List.Tot.for_all (opt_map_entry_bounded b) x })
: Lemma
  (requires (List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) x))
  (ensures (
    begin match Cbor.list_ghost_assoc k x with
    | None -> True
    | Some y -> opt_precedes y b /\ List.Tot.sorted (Cbor.map_entry_order Cbor.deterministically_encoded_cbor_map_key_order _) (List.Tot.filter (map_key_neq _ k) x)
    end /\
    matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x ==
    begin match Cbor.list_ghost_assoc k x with
    | None -> false
    | Some y -> ty y && matches_map_group g (List.Tot.filter (map_key_neq _ k) x)
    end
  ))
  [SMTPat (matches_map_group (map_group_cons_one (map_group_entry_for k ty) true g) x)]

// 2.1 specifies "names that turn into the map key text string"

noextract
let string64 = (s: Seq.seq U8.t {FStar.UInt.fits (Seq.length s) 64})

let name_as_text_string (s: string64) : typ =
  t_literal (Cbor.String Cbor.major_type_text_string s)

let t_map (#b: option Cbor.raw_data_item) (m: map_group b) : bounded_typ_gen b = fun x ->
  Cbor.Map? x &&
  matches_map_group m (Cbor.Map?.v x)

let t_map_equiv #b (m1 m2: map_group b) : Lemma
  (requires (map_group_equiv m1 m2))
  (ensures (typ_equiv (t_map m1) (t_map m2)))
= ()

let rec t_map_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> map_group (Some b)))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Map? x &&
  matches_map_group (phi x (t_map_rec phi)) (Cbor.Map?.v x)

// Section 3.6: Tags

let t_tag (#b: option Cbor.raw_data_item) (tag: U64.t) (t: bounded_typ_gen b) : bounded_typ_gen b = fun x ->
  Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  t (Cbor.Tagged?.v x)

let rec t_tag_rec
  (tag: U64.t)
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> bounded_typ b))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Tagged? x &&
  Cbor.Tagged?.tag x = tag &&
  phi x (t_tag_rec tag phi) (Cbor.Tagged?.v x)

// Multi-purpose recursive combinator, to allow disjunctions between destructors

let rec multi_rec
  (phi_base: typ)
  (phi_array: (b: Cbor.raw_data_item) -> bounded_typ b -> array_group3 (Some b))
  (phi_map: (b: Cbor.raw_data_item) -> bounded_typ b -> map_group (Some b))
  (phi_tag: U64.t -> (b: Cbor.raw_data_item) -> bounded_typ b -> bounded_typ b)
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= phi_base x ||
  begin match x with
  | Cbor.Array v ->
    match_array_group3 (phi_array x (multi_rec phi_base phi_array phi_map phi_tag)) v
  | Cbor.Map v ->
    matches_map_group (phi_map x (multi_rec phi_base phi_array phi_map phi_tag)) v
  | Cbor.Tagged tag v ->
    phi_tag tag x (multi_rec phi_base phi_array phi_map phi_tag) v
  | _ -> false
  end

// Section 3.8.1: Control .size

let str_size (ty: Cbor.major_type_byte_string_or_text_string) (sz: nat) : typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = ty &&
  Seq.length (Cbor.String?.v x) = sz

let uint_size (sz: nat) : typ = fun x ->
  Cbor.Int64? x &&
  Cbor.Int64?.typ x = Cbor.major_type_uint64 &&
  U64.v (Cbor.Int64?.v x) < pow2 sz

// Section 3.8.4: Control .cbor
// We parameterize over the CBOR order on which the CBOR parser depends

let bstr_cbor
  (data_item_order: (Cbor.raw_data_item -> Cbor.raw_data_item -> bool))
  (ty: typ) // TODO: enable recursion for this construct? If so, we need to replace << with some serialization size
: typ = fun x ->
  Cbor.String? x &&
  Cbor.String?.typ x = Cbor.major_type_byte_string &&
  FStar.StrongExcludedMiddle.strong_excluded_middle (
    exists y . Cbor.serialize_cbor y == Cbor.String?.v x /\
    Cbor.data_item_wf data_item_order y /\
    ty y == true
  )
