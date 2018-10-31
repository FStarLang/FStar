module LowParse.Spec.Enum
include LowParse.Spec.Combinators

module L = FStar.List.Tot

inline_for_extraction
let eqtype : Type u#1 = (t: Type0 { hasEq t } )
// eqtype u#0 // does not extract to OCaml

noeq
type norm_t : Type0 = | Norm

[@Norm]
let rec list_map
  (#a #b: Type)
  (f: (a -> Tot b))
  (l: list a)
: Tot (l' : list b { l' == L.map f l } )
= match l with
  | [] -> []
  | a :: q -> f a :: list_map f q

type enum (key: eqtype) (repr: eqtype) = (l: list (key * repr) {
  L.noRepeats (list_map fst l) /\
  L.noRepeats (list_map snd l)
})

[@Norm]
let rec list_mem
  (#t: eqtype)
  (x: t)
  (l: list t)
: Tot (y: bool { y == true <==> L.mem x l == true } )
= match l with
  | [] -> false
  | a :: q -> (x = a || list_mem x q)

let norm_spec
  (#t: Type)
  (x: t)
: Lemma
  (norm [delta_attr [`%Norm]; iota; zeta; primops] x == x)
= norm_spec [delta_attr [`%Norm]; iota; zeta; primops] x

inline_for_extraction
let enum_key (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (s: key { list_mem s (list_map fst e) } )

inline_for_extraction
let enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot eqtype = (r: repr { list_mem r (list_map snd e) } )

let flip (#a #b: Type) (c: (a * b)) : Tot (b * a) = let (ca, cb) = c in (cb, ca)

let rec map_flip_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map flip (list_map flip l) == l)
= match l with
  | [] -> ()
  | _ :: q -> map_flip_flip q

let rec map_fst_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map fst (list_map flip l) == list_map snd l)
= match l with
  | [] -> ()
  | _ :: q -> map_fst_flip q

let rec map_snd_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (list_map snd (list_map flip l) == list_map fst l)
= match l with
  | [] -> ()
  | _ :: q -> map_snd_flip q

let rec assoc_mem_snd
  (#a #b: eqtype)
  (l: list (a * b))
  (x: a)
  (y: b)
: Lemma
  (requires (L.assoc x l == Some y))
  (ensures (list_mem y (list_map snd l) == true))
  (decreases l)
= let ((x', y') :: l') = l in
  if x' = x
  then ()
  else assoc_mem_snd l' x y

let rec assoc_flip_elim
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc y (list_map flip l) == Some x
  ))
  (ensures (
    L.assoc x l == Some y
  ))
  (decreases l)
= let ((x', y') :: l') = l in
  if y' = y
  then ()
  else begin
    if x' = x
    then begin
      assert (list_mem x' (list_map fst l') == false);
      assoc_mem_snd (list_map flip l') y x;
      map_snd_flip l';
      assert False
    end
    else
      assoc_flip_elim l' y x
  end

let rec assoc_flip_intro
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    L.noRepeats (list_map fst l) /\
    L.noRepeats (list_map snd l) /\
    L.assoc x l == Some y
  ))
  (ensures (
    L.assoc y (list_map flip l) == Some x
  ))
= map_fst_flip l;
  map_snd_flip l;
  map_flip_flip l;
  assoc_flip_elim (list_map flip l) x y

let enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Pure (enum_key e)
  (requires True)
  (ensures (fun y -> L.assoc y e == Some r))
= map_fst_flip e;
  let e' = list_map flip e in
  L.assoc_mem r e';
  let k = Some?.v (L.assoc r e') in
  assoc_flip_elim e r k;
  L.assoc_mem k e;
  (k <: enum_key e)

let parse_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser (parse_filter_kind k) (enum_key e))
= (p
    `parse_filter`
    (fun (r: repr) -> list_mem r (list_map snd e))
  )
  `parse_synth`
  (fun (x: repr {list_mem x (list_map snd e) == true})  -> enum_key_of_repr e x)

let enum_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Pure (enum_repr e)
  (requires True)
  (ensures (fun r -> L.assoc k e == Some r))
= L.assoc_mem k e;
  let r = Some?.v (L.assoc k e) in
  assoc_flip_intro e r k;
  L.assoc_mem r (list_map flip e);
  map_fst_flip e;
  (r <: enum_repr e)

let enum_repr_of_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let bare_serialize_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (bare_serializer (enum_key e))
= fun (k: enum_key e) -> s (enum_repr_of_key e k)

#set-options "--z3rlimit 32"

let bare_serialize_enum_key_correct
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Lemma
  (serializer_correct (parse_enum_key p e) (bare_serialize_enum_key p s e))
= Classical.forall_intro (enum_key_of_repr_of_key e)

#reset-options

let serialize_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_enum_key p e))
= bare_serialize_enum_key_correct p s e;
  bare_serialize_enum_key p s e

inline_for_extraction
let unknown_enum_repr (#key #repr: eqtype) (e: enum key repr) : Tot Type0 =
  (r: repr { list_mem r (list_map snd e) == false } )

type maybe_enum_key (#key #repr: eqtype) (e: enum key repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_repr e)

let maybe_enum_key_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (r: repr)
: Tot (maybe_enum_key e)
= if list_mem r (list_map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r

let parse_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
: Tot (parser k (maybe_enum_key e))
= p `parse_synth` (maybe_enum_key_of_repr e)

let repr_of_maybe_enum_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (x: maybe_enum_key e)
: Tot (r: repr { maybe_enum_key_of_repr e r == x } )
= match x with
  | Known k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | Unknown r -> r

let serialize_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: enum key repr)
: Tot (serializer (parse_maybe_enum_key p e))
= serialize_synth p (maybe_enum_key_of_repr e) s (repr_of_maybe_enum_key e) ()

let is_total_enum (#key: eqtype) (#repr: eqtype) (l: list (key * repr)) : GTot Type0 =
  forall (k: key) . list_mem k (list_map fst l)

let total_enum (key: eqtype) (repr: eqtype) : Tot eqtype =
  (l: enum key repr { is_total_enum l } )

let synth_total_enum_key
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: enum_key l)
: Tot key
= let k' : key = k in
  k'

let parse_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (l: total_enum key repr)
: Tot (parser (parse_filter_kind k) key)
= parse_enum_key p l `parse_synth` (synth_total_enum_key l)

let synth_total_enum_key_recip
  (#key: eqtype)
  (#repr: eqtype)
  (l: total_enum key repr)
  (k: key)
: Tot (k' : enum_key l { synth_total_enum_key l k' == k } )
= k

let serialize_total_enum_key
  (#k: parser_kind)
  (#key: eqtype)
  (#repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (l: total_enum key repr)
: Tot (serializer (parse_total_enum_key p l))
= serialize_synth (parse_enum_key p l) (synth_total_enum_key l) (serialize_enum_key p s l) (synth_total_enum_key_recip l) ()

type maybe_total_enum_key (#key #repr: eqtype) (e: total_enum key repr) =
| TotalKnown of key
| TotalUnknown of (unknown_enum_repr e)

let maybe_total_enum_key_of_repr
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (r: repr)
: Tot (maybe_total_enum_key e)
= if list_mem r (list_map snd e)
  then TotalKnown (enum_key_of_repr e r)
  else TotalUnknown r

let parse_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: total_enum key repr)
: Tot (parser k (maybe_total_enum_key e))
= p `parse_synth` (maybe_total_enum_key_of_repr e)

let repr_of_maybe_total_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (r: repr { maybe_total_enum_key_of_repr e r == k } )
= match k with
  | TotalKnown k' ->
    enum_key_of_repr_of_key e k' ;
    enum_repr_of_key e k'
  | TotalUnknown r -> r

let serialize_maybe_total_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (s: serializer p)
  (e: total_enum key repr)
: Tot (serializer (parse_maybe_total_enum_key p e))
= serialize_synth p (maybe_total_enum_key_of_repr e) s (repr_of_maybe_total_enum_key e) ()

let weaken_maybe_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (k: maybe_total_enum_key e)
: Tot (maybe_enum_key e)
= match k with
  | TotalKnown ek -> Known (ek <: key)
  | TotalUnknown r -> Unknown r
