module Map.OpaqueToSMT
module M = Map

[@"opaque_to_smt"]
let map k v = M.map k v

[@"opaque_to_smt"]
let sel = M.sel

[@"opaque_to_smt"]
let upd = M.upd

let sel_upd1 (#k:eqtype) (#v:Type) (m:map k v) (key:k) (value:v)
  : Lemma
    (ensures (sel (upd m key value) key == value))
    [SMTPat (sel (upd m key value) key)]
  = assert_norm (sel (upd m key value) key == M.sel (M.upd m key value) key)

let sel_upd2 (#k:eqtype) (#v:Type) (m:map k v) (key1:k) (key2:k) (value:v)
  : Lemma
    (ensures (~(key1 == key2) ==> sel (upd m key1 value) key2 == sel m key2))
    [SMTPat (sel (upd m key1 value) key2)]
  = assert_norm (sel (upd m key1 value) key2 == M.sel (M.upd m key1 value) key2);
    assert_norm (sel m key2 == M.sel m key2)
  


