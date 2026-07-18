open Prims
type ('key, 'value) t =
  {
  mappings: ('key, 'value) FStar_FunctionalExtensionality.restricted_t ;
  domain: 'key FStar_Set.set }
let __proj__Mkt__item__mappings (projectee : ('key, 'value) t) :
  ('key, 'value) FStar_FunctionalExtensionality.restricted_t=
  match projectee with | { mappings; domain;_} -> mappings
let __proj__Mkt__item__domain (projectee : ('key, 'value) t) :
  'key FStar_Set.set= match projectee with | { mappings; domain;_} -> domain
let sel (m : ('key, 'value) t) (k : 'key) : 'value= m.mappings k
let upd (m : ('key, 'value) t) (k : 'key) (v : 'value) : ('key, 'value) t=
  {
    mappings = (fun x -> if x = k then v else m.mappings x);
    domain = (FStar_Set.union m.domain (FStar_Set.singleton k))
  }
let const (v : 'value) : ('key, 'value) t=
  {
    mappings = (fun x -> v);
    domain = (FStar_Set.complement (FStar_Set.empty ()))
  }
let domain (m : ('key, 'value) t) : 'key FStar_Set.set= m.domain
let contains (m : ('key, 'value) t) (k : 'key) : Prims.bool=
  FStar_Set.mem k m.domain
let concat (m1 : ('key, 'value) t) (m2 : ('key, 'value) t) :
  ('key, 'value) t=
  {
    mappings =
      (fun x ->
         if FStar_Set.mem x m2.domain then m2.mappings x else m1.mappings x);
    domain = (FStar_Set.union m1.domain m2.domain)
  }
let map_val (f : 'uuuuu -> 'uuuuu1) (key : unit) (m : (Obj.t, 'uuuuu) t) :
  (Obj.t, 'uuuuu1) t=
  { mappings = (fun x -> f (m.mappings x)); domain = (m.domain) }
let restrict (s : 'key FStar_Set.set) (m : ('key, 'value) t) :
  ('key, 'value) t=
  { mappings = (m.mappings); domain = (FStar_Set.intersect s m.domain) }
let const_on (dom : 'key FStar_Set.set) (v : 'value) : ('key, 'value) t=
  restrict dom (const v)
let map_literal (f : 'k -> 'v) : ('k, 'v) t=
  {
    mappings = (fun x -> f x);
    domain = (FStar_Set.complement (FStar_Set.empty ()))
  }
