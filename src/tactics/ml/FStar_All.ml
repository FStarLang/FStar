open Prims
type all_pre = FStar_Heap.heap FStar_Pervasives.all_pre_h
type 'Aa all_post = (FStar_Heap.heap,'Aa) FStar_Pervasives.all_post_h
type 'Aa all_wp = (FStar_Heap.heap,'Aa) FStar_Pervasives.all_wp_h
type ('Aa,'Awp,'Ap) lift_state_all = 'Awp
type ('Aa,'Awp,'Ap,'Ah) lift_exn_all = 'Awp
let pipe_right uu____66 uu____67 = failwith "Not yet implemented:pipe_right"
let pipe_left uu____94 uu____95 = failwith "Not yet implemented:pipe_left"
let failwith uu____112 = failwith "Not yet implemented:failwith"
let exit uu____123 = failwith "Not yet implemented:exit"
let try_with uu____148 uu____149 = failwith "Not yet implemented:try_with"