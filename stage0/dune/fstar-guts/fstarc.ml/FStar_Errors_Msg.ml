open Prims
type error_message = FStar_Pprint.document Prims.list
let text (s : Prims.string) : FStar_Pprint.document=
  FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
    (FStar_Pprint.words s)
let mkmsg (s : Prims.string) : error_message=
  [FStar_Pprint.arbitrary_string s]
