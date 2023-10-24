module CDDL.Spec
module Cbor = CBOR.Spec
module U8 = FStar.UInt8
module U64 = FStar.UInt64

// Concise Data Definition Language (RFC 8610)

[@@noextract_to "krml"]
let typ = (Cbor.raw_data_item -> GTot bool) // GTot needed because of the .cbor control (staged serialization)
let bounded_typ (e: Cbor.raw_data_item) = ((e': Cbor.raw_data_item { e' << e }) -> GTot bool)
let t_choice (t1 t2: typ) : typ = (fun x -> t1 x || t2 x)
let t_bounded_choice (e: Cbor.raw_data_item) (t1 t2: bounded_typ e) : bounded_typ e = (fun x -> t1 x || t2 x)
let t_always_false : typ = (fun _ -> false)

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
  (fun x -> Cbor.Simple? x && Cbor.Simple?.v x = s)

let t_false : typ = t_simple_value_literal simple_value_false
let t_true : typ = t_simple_value_literal simple_value_true
let t_bool : typ = t_choice t_false t_true
let t_nil : typ = t_simple_value_literal simple_value_nil
let t_null : typ = t_nil
let t_undefined : typ = t_simple_value_literal simple_value_undefined

let t_uint_literal (v: U64.t) : typ = (fun x ->
  uint x &&
  Cbor.Int64?.v x = v
)

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
let array_group3 (bound: Cbor.raw_data_item) = (l: list Cbor.raw_data_item { l << bound }) -> Ghost (option (list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with
  | None -> True
  | Some l' -> l' << bound
  ))
let array_group3_always_false #b : array_group3 b = fun _ -> None
let array_group3_empty #b : array_group3 b = fun x -> Some x
let array_group3_concat #b (a1 a3: array_group3 b) : array_group3 b =
  (fun l ->
    match a1 l with
    | None -> None
    | Some l3 -> a3 l3
  )

let array_group3_choice #b (a1 a3: array_group3 b) : array_group3 b =
  fun l -> match a1 l with
    | None -> a3 l
    | Some l3 -> Some l3

let rec array_group3_zero_or_more' #b (a: array_group3 b) (l: list Cbor.raw_data_item { l << b }) : Ghost (option (list Cbor.raw_data_item))
  (requires True)
  (ensures (fun l' -> match l' with None -> True | Some l' -> l' << b))
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

let array_group3_item (#b: Cbor.raw_data_item) (t: bounded_typ b) : array_group3 b = fun l ->
  match l with
  | [] -> None
  | a :: q -> if t a then Some q else None

let match_array_group3 (#b: Cbor.raw_data_item) (a: array_group3 b)
  (l: list Cbor.raw_data_item {l << b})
: GTot bool
= match a l with
  | Some l' -> Nil? l
  | _ -> false

let t_array3_bounded (#b: Cbor.raw_data_item) (a: array_group3 b) : bounded_typ b = fun x ->
  Cbor.Array? x &&
  match_array_group3 a (Cbor.Array?.v x)

// Recursive type (needed by COSE Section 5.1 "Recipient")

// Inspiring from Barthe et al., Type-Based Termination with Sized
// Products (CSL 2008): we allow recursion only at the level of
// destructors. In other words, instead of having a generic recursion
// combinator, we provide a recursion-enabled version only for each
// destructor combinator. We need to annotate it with a bound b (akin
// to the "size" annotation in a sized type.)

let rec t_array3_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> array_group3 b))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
=
  Cbor.Array? x &&
  match_array_group3 (phi x (t_array3_rec phi)) (Cbor.Array?.v x)

let t_array3
  (phi: (b: Cbor.raw_data_item) -> array_group3 b)
: Tot typ
= t_array3_rec (fun b _ -> phi b)

// Groups in map context (Section 3.5)

[@@erasable]
noeq
type map_group_entry (b: Cbor.raw_data_item) = | MapGroupEntry: (fst: bounded_typ b) -> (snd: bounded_typ b) -> map_group_entry b

let matches_map_group_entry
  (#b: Cbor.raw_data_item)
  (ge: map_group_entry b)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item) { x << b })
: GTot bool
= ge.fst (fst x) && ge.snd (snd x)

[@@erasable]
noeq
type map_group (b: Cbor.raw_data_item) = {
  one: list (map_group_entry b);
  zero_or_one: list (map_group_entry b);
  zero_or_more: list (map_group_entry b);
}

let map_group_empty #b : map_group b = {
  one = [];
  zero_or_one = [];
  zero_or_more = [];
}

// Section 3.5.4: Cut
let cut_map_group_entry #b (key: bounded_typ b) (ge: map_group_entry b) : map_group_entry b =
  (fun x -> ge.fst x && not (key x)) `MapGroupEntry` ge.snd

let cut_map_group #b (key: bounded_typ b) (g: map_group b) : map_group b = {
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

let rec matches_list_map_group_entry'
  (#b: Cbor.raw_data_item)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item) { x << b })
  (unmatched: list (map_group_entry b))
  (l: list (map_group_entry b))
: GTot (option (list (map_group_entry b)))
  (decreases l)
= match l with
  | [] -> None
  | a :: q ->
    if matches_map_group_entry a x
    then Some (List.Tot.rev_acc unmatched q)
    else matches_list_map_group_entry' x (a :: unmatched) q

let matches_list_map_group_entry
  (#b: Cbor.raw_data_item)
  (x: (Cbor.raw_data_item & Cbor.raw_data_item) { x << b })
  (l: list (map_group_entry b))
: GTot (option (list (map_group_entry b)))
= matches_list_map_group_entry' x [] l

let rec ghost_list_exists (#a: Type) (f: (a -> GTot bool)) (l: list a): GTot bool = match l with
 | [] -> false
 | hd::tl -> if f hd then true else ghost_list_exists f tl

let rec matches_map_group
  (#b: Cbor.raw_data_item)
  (m: map_group b)
  (x: list (Cbor.raw_data_item & Cbor.raw_data_item) {x << b })
: GTot bool
  (decreases x)
= match x with
  | [] -> Nil? m.one
  | a :: q ->
    begin match matches_list_map_group_entry a m.one with
      | None -> false
      | Some one' -> matches_map_group ({m with one = one'}) q
    end ||
    begin match matches_list_map_group_entry a m.zero_or_one with
      | None -> false
      | Some one' -> matches_map_group ({m with zero_or_one = one'}) q
    end || (
      ghost_list_exists (fun x -> matches_map_group_entry x a) m.zero_or_more &&
      matches_map_group m q
    )

// 2.1 specifies "names that turn into the map key text string"
let name_as_text_string (s: Seq.seq U8.t) : typ = (fun x -> tstr x && Cbor.String?.v x = s)

let t_map_bounded (#b: Cbor.raw_data_item) (m: map_group b) : bounded_typ b = fun x ->
  Cbor.Map? x &&
  matches_map_group m (Cbor.Map?.v x)

let rec t_map_rec
  (phi: (b: Cbor.raw_data_item) -> (bounded_typ b -> map_group b))
  (x: Cbor.raw_data_item)
: GTot bool
  (decreases x)
= Cbor.Map? x &&
  matches_map_group (phi x (t_map_rec phi)) (Cbor.Map?.v x)

let t_map
  (phi: (b: Cbor.raw_data_item) -> map_group b)
: Tot typ
= t_map_rec (fun b _ -> phi b)

// Section 3.6: Tags

let t_tag_bounded (#b: Cbor.raw_data_item) (tag: U64.t) (t: bounded_typ b) : bounded_typ b = fun x ->
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

let t_tag
  (tag: U64.t)
  (phi: (b: Cbor.raw_data_item) -> bounded_typ b)
: Tot typ
= t_tag_rec tag (fun b _ -> phi b)

// Multi-purpose recursive combinator, to allow disjunctions between destructors

let rec multi_rec
  (phi_base: typ)
  (phi_array: (b: Cbor.raw_data_item) -> bounded_typ b -> array_group3 b)
  (phi_map: (b: Cbor.raw_data_item) -> bounded_typ b -> map_group b)
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
