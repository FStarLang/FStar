module FStar.DependentMap

noeq abstract type t (key:eqtype) (value: (key -> Type)) =
{
  mappings: (k: key) -> Tot (value k)
}

abstract let create
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (f: ((k: key) -> Tot (value k)))
: Tot (t key value)
= {
  mappings = f
}

abstract let sel
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m: t key value)
  (k: key)
: Tot (value k)
= m.mappings k

abstract let sel_create
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (f: ((k: key) -> Tot (value k)))
  (k: key)
: Lemma
  (requires True)
  (ensures (sel #key #value (create f) k == f k))
  [SMTPat (sel (create f) k)]
= ()

abstract let upd
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m: t key value)
  (k: key)
  (v: value k)
: Tot (t key value)
= {
  mappings = (fun k' -> if k' = k then v else m.mappings k')
}

abstract let sel_upd_same
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m: t key value)
  (k: key)
  (v: value k)
: Lemma
  (requires True)
  (ensures (sel (upd m k v) k == v))
  [SMTPat (sel (upd m k v) k)]
= ()

abstract let sel_upd_other
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m: t key value)
  (k: key)
  (v: value k)
  (k': key)
: Lemma
  (requires (k' <> k))
  (ensures (sel (upd m k v) k' == sel m k'))
  [SMTPat (sel (upd m k v) k')]
= ()

abstract let equal
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m1 m2: t key value)
: Tot Type0
= forall k . sel m1 k == sel m2 k

abstract let equal_intro
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m1 m2: t key value)
: Lemma
  (requires (forall k . sel m1 k == sel m2 k))
  (ensures (equal m1 m2))
  [SMTPat (equal m1 m2)]
= ()

abstract let equal_refl
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m: t key value)
: Lemma
  (ensures (equal m m))
  [SMTPat (equal m m)]
= ()

(** TODO: we need dependent functional extensionality *)

assume val equal_elim
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (m1 m2: t key value)
: Lemma
  (requires (equal m1 m2))
  (ensures (m1 == m2))
  [SMTPat (equal m1 m2)]

abstract let restrict
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: (key -> Tot Type0))
  (m: t key value)
: Tot (t (k: key {p k}) value)
= { mappings = m.mappings }

abstract let sel_restrict
  (#key: eqtype)
  (#value: (key -> Tot Type))
  (p: (key -> Tot Type0))
  (m: t key value)
  (k: key {p k})
: Lemma
  (requires True)
  (ensures (sel (restrict p m) k == sel m k))
= ()

let concat_value
  (#key1: eqtype)
  (value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (value2: (key2 -> Tot Type))
  (k: either key1 key2)
: Tot Type
= match k with
  | Inl k1 -> value1 k1
  | Inr k2 -> value2 k2

private let concat_mappings
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (#value2: (key2 -> Tot Type))
  (m1: (k1: key1) -> Tot (value1 k1))
  (m2: (k2: key2) -> Tot (value2 k2))
  (k: either key1 key2)
: Tot (concat_value value1 value2 k)
= match k with
  | Inl k1 -> m1 k1
  | Inr k2 -> m2 k2

abstract let concat
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (#value2: (key2 -> Tot Type))
  (m1: t key1 value1)
  (m2: t key2 value2)
: Tot (t (either key1 key2) (concat_value value1 value2))
= { mappings = concat_mappings m1.mappings m2.mappings  }

abstract let sel_concat_l
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (#value2: (key2 -> Tot Type))
  (m1: t key1 value1)
  (m2: t key2 value2)
  (k1: key1)
: Lemma
  (requires True)
  (ensures (sel (concat m1 m2) (Inl k1) == sel m1 k1))
= ()

abstract let sel_concat_r
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (#value2: (key2 -> Tot Type))
  (m1: t key1 value1)
  (m2: t key2 value2)
  (k2: key2)
: Lemma
  (requires True)
  (ensures (sel (concat m1 m2) (Inr k2) == sel m2 k2))
= ()

let rename_value
  (#key1: eqtype)
  (value1: (key1 -> Tot Type))
  (#key2: eqtype)
  (ren: key2 -> Tot key1)
  (k: key2)
: Tot Type
= value1 (ren k)

abstract let rename
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (m: t key1 value1)
  (#key2: eqtype)
  (ren: key2 -> Tot key1)
: Tot (t key2 (rename_value value1 ren))
= { mappings = fun k2 -> m.mappings (ren k2) }

abstract let sel_rename
  (#key1: eqtype)
  (#value1: (key1 -> Tot Type))
  (m: t key1 value1)
  (#key2: eqtype)
  (ren: key2 -> Tot key1)
  (k2: key2)
: Lemma
  (ensures (sel (rename m ren) k2 == sel m (ren k2)))
= ()

abstract let map
  (#key: eqtype)
  (#value1 #value2: (key -> Tot Type))
  (f: (k: key) -> value1 k -> Tot (value2 k))
  (m: t key value1)
: Tot (t key value2)
= {
  mappings = fun k -> f k (sel m k)
}

abstract let sel_map
  (#key: eqtype)
  (#value1 #value2: (key -> Tot Type))
  (f: (k: key) -> value1 k -> Tot (value2 k))
  (m: t key value1)
  (k: key)
: Lemma
  (requires True)
  (ensures (sel (map f m) k == f k (sel m k)))
  [SMTPat (sel (map f m) k)]
= ()

abstract let map_upd
  (#key: eqtype)
  (#value1 #value2: (key -> Tot Type))
  (f: (k: key) -> value1 k -> Tot (value2 k))
  (m: t key value1)
  (k: key)
  (v: value1 k)
: Lemma
  (requires True)
  (ensures (map f (upd m k v) == upd (map f m) k (f k v)))
  [SMTPat (map f (upd m k v))]  //AR: wanted to write an SMTPatOr, but gives some error
= equal_elim #key #value2 (map f (upd m k v)) (upd (map f m) k (f k v))
