
open Prims

let prime : Prims.pos FStar_Ghost.erased = (Obj.magic (()))


let platform_size : Prims.pos = (Prims.parse_int "64")


let platform_wide : Prims.pos = (Prims.parse_int "128")


let norm_length : Prims.pos = (Prims.parse_int "5")


let nlength : FStar_UInt32.t = (FStar_UInt32.uint_to_t (Prims.parse_int "5"))


let bytes_length : Prims.pos = (Prims.parse_int "32")


let blength : FStar_UInt32.t = (FStar_UInt32.uint_to_t (Prims.parse_int "32"))


let templ : Prims.nat  ->  Prims.pos = (fun i -> (Prims.parse_int "51"))


let a24' : Prims.int = (Prims.parse_int "121665")


let a24 : FStar_UInt64.t = (FStar_UInt64.uint_to_t (Prims.parse_int "121665"))


let parameters_lemma_0 : Prims.unit  ->  Prims.unit = (fun uu____38 -> ())


let parameters_lemma_1 : Prims.unit  ->  Prims.unit = (fun uu____41 -> ())




