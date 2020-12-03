#light "off"
module FStar_Map
open Prims
open FStar_Pervasives
(* TODO: The extracted version of this file doesn't include the when 'key : comparison constraint which is required for F# *)
type t<'key, 'value when 'key : comparison> =
{mappings : ('key, 'value) FStar_FunctionalExtensionality.restricted_t; domain : 'key FStar_Set.set}


let __proj__Mkt__item__mappings = (fun ( projectee  :  ('key, 'value) t ) -> (match (projectee) with
| {mappings = mappings; domain = domain} -> begin
mappings
end))


let __proj__Mkt__item__domain = (fun ( projectee  :  ('key, 'value) t ) -> (match (projectee) with
| {mappings = mappings; domain = domain} -> begin
domain
end))


let sel = (fun ( m  :  ('key, 'value) t ) ( k  :  'key ) -> (m.mappings k))


let upd = (fun ( m  :  ('key, 'value) t ) ( k  :  'key ) ( v  :  'value ) -> {mappings = (FStar_FunctionalExtensionality.on_domain (fun ( x  :  'key ) -> (match ((Prims.op_Equality x k)) with
| true -> begin
v
end
| uu____5020 -> begin
(m.mappings x)
end))); domain = (FStar_Set.union m.domain (FStar_Set.singleton k))})


let const1 = (fun ( v  :  'value ) -> {mappings = (FStar_FunctionalExtensionality.on_domain (fun ( uu____5049  :  'key ) -> v)); domain = (FStar_Set.complement (FStar_Set.empty ()))})


let domain = (fun ( m  :  ('key, 'value) t ) -> m.domain)


let contains = (fun ( m  :  ('key, 'value) t ) ( k  :  'key ) -> (FStar_Set.mem k m.domain))


let concat = (fun ( m1  :  ('key, 'value) t ) ( m2  :  ('key, 'value) t ) -> {mappings = (FStar_FunctionalExtensionality.on_domain (fun ( x  :  'key ) -> (match ((FStar_Set.mem x m2.domain)) with
| true -> begin
(m2.mappings x)
end
| uu____5174 -> begin
(m1.mappings x)
end))); domain = (FStar_Set.union m1.domain m2.domain)})

(* TODO: Only implicit arguments at the start of a function are erased, whereas the others are extracted to unit and obj 
         which makes extracted function unusable. See examples/hello/TestFSharp for a minimal example. 

         Here, key should be a generic argument with a comparison constraint instead of obj/unit. 

         A simple workaround would be to change the declaration of map_val in the FStar.Map.fsti so that 
         '#key:eqtype' parameter is moved before any non-implicit parameters (i.e. before 'f').
*)
let map_val = (fun ( f  :  'uuuuuu5195  ->  'uuuuuu5196 ) ( key  :  'key ) ( m  :  ('key, 'uuuuuu5195) t ) -> {mappings = (FStar_FunctionalExtensionality.on_domain (fun ( x  :  'key ) -> (f (m.mappings x)))); domain = m.domain})


let restrict = (fun ( s  :  'key FStar_Set.set ) ( m  :  ('key, 'value) t ) -> {mappings = m.mappings; domain = (FStar_Set.intersect s m.domain)})


let const_on = (fun ( dom  :  'key FStar_Set.set ) ( v  :  'value ) -> (restrict dom (const1 v)))


type disjoint_dom =
unit


type has_dom =
unit















































type equal =
unit













