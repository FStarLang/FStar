module Map

type map (k:eqtype) (v:Type) = k -> v

let sel (#k:eqtype) (#v:Type) (m:map k v) (key:k) : v = m key

let upd (#k:eqtype) (#v:Type) (m:map k v) (key:k) (value:v) : map k v =
  fun x -> if x = key then value else sel m x

let sel_upd1 (#k:eqtype) (#v:Type) (m:map k v) (key:k) (value:v)
  : Lemma
    (ensures (sel (upd m key value) key == value))
    [SMTPat (sel (upd m key value) key)]
  = ()

let sel_upd2 (#k:eqtype) (#v:Type) (m:map k v) (key1:k) (key2:k) (value:v)
  : Lemma
    (ensures (~(key1 == key2) ==> sel (upd m key1 value) key2 == sel m key2))
    [SMTPat (sel (upd m key1 value) key2)]
  = ()
