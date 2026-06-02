module Bug4239Variant

#lang-pulse
open Pulse
module FE = FStar.FunctionalExtensionality

assume val rel : Type0 -> Type0 -> Type0
let type_spec (impl_elt: Type0) = dtuple2 Type0 (rel impl_elt)

let mk_spec
  (#impl_elt: Type0)
  (#src_elt: Type0)
  (r: rel impl_elt src_elt)
: Tot (Ghost.erased (type_spec impl_elt))
= Ghost.hide (| _, r |)

let eq_test_for (#t: Type) (x1: t) : Type =
  FE.restricted_t t (fun x2 -> (y: bool { y == true <==> x1 == x2 }))

let eq_test (t: Type) : Type =
  FE.restricted_t t (fun x1 -> eq_test_for x1)

let mk_iterator 
    (#tkey: Type0)
    (key_eq: Ghost.erased (eq_test tkey))
    (#ikey: Type0)
    (#r1: rel ikey tkey)
= 
 let kk : Ghost.erased (eq_test (dfst (mk_spec r1))) = key_eq in
 ()

fn mk_iterator2
  (#tkey: Type0)
    (key_eq: Ghost.erased (eq_test tkey))
    (#ikey: Type0)
    (#r1: rel ikey tkey)
{
 let kk : Ghost.erased (eq_test (dfst (mk_spec r1))) = key_eq;
 ()
}