open Prims
type 'Aa ref = 'Aa FStar_Heap.ref
type ('Ah0,'Ah1) modifies_none = Prims.unit
type st_pre = FStar_Heap.heap FStar_Pervasives.st_pre_h
type 'Aa st_post = (FStar_Heap.heap,'Aa) FStar_Pervasives.st_post_h
type 'Aa st_wp = (FStar_Heap.heap,'Aa) FStar_Pervasives.st_wp_h
type ('Aa,'Awp,'Ap,'Ah) lift_div_state = 'Awp
let recall r = failwith "Not yet implemented:recall"
let alloc init = failwith "Not yet implemented:alloc"
let read r = failwith "Not yet implemented:read"
let write r v = failwith "Not yet implemented:write"
let get: Prims.unit -> FStar_Heap.heap =
  fun uu____131  -> failwith "Not yet implemented:get"