open Prims
type all_pre = FStar_Heap.heap FStar_Pervasives.all_pre_h
type 'Aa all_post = (FStar_Heap.heap,'Aa) FStar_Pervasives.all_post_h
type 'Aa all_wp = (FStar_Heap.heap,'Aa) FStar_Pervasives.all_wp_h
type ('Aa,'Awp,'Ap) lift_state_all = 'Awp
type ('Aa,'Awp,'Ap,'Ah) lift_exn_all = 'Awp
let pipe_right uu____70 uu____71 = failwith "Not yet implemented:pipe_right"
let pipe_left uu____102 uu____103 = failwith "Not yet implemented:pipe_left"
let failwith uu____122 = failwith "Not yet implemented:failwith"
let exit uu____135 = failwith "Not yet implemented:exit"
let try_with uu____163 uu____164 = failwith "Not yet implemented:try_with"