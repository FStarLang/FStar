type u8 = FStar_UInt_UInt8.uint8
type u16 = FStar_UInt_UInt16.uint16
type u32 = FStar_UInt_UInt32.uint32
type u63 = FStar_UInt_UInt63.uint63
type u64 = FStar_UInt_UInt64.uint64
type i8 = FStar_Int_Int8.int8
type i16 = FStar_Int_Int16.int16
type i32 = FStar_Int_Int32.int32
type i63 = FStar_Int_Int63.int63
type i64 = FStar_Int_Int64.int64

let test_uint8 () =
  let zero = FStar_UInt_UInt8.int_to_uint8 (Prims.parse_int "0") in
  let one = FStar_UInt_UInt8.int_to_uint8 (Prims.parse_int "1") in
  let ones = FStar_UInt_UInt8.int_to_uint8 (Prims.parse_int "255") in  
  let ones' = FStar_UInt_UInt8.sub_mod zero one in
  let zero' = FStar_UInt_UInt8.add_mod ones one in
  let ones_square = FStar_UInt_UInt8.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 255 255\nGot:     %s %s %s %s %s %s\n"
                (FStar_UInt_UInt8.to_string zero)
                (FStar_UInt_UInt8.to_string zero')
                (FStar_UInt_UInt8.to_string one)
                (FStar_UInt_UInt8.to_string ones_square)
                (FStar_UInt_UInt8.to_string ones)
                (FStar_UInt_UInt8.to_string ones');
  ()

let test_uint16 () =
  let zero = FStar_UInt_UInt16.int_to_uint16 (Prims.parse_int "0") in
  let one = FStar_UInt_UInt16.int_to_uint16 (Prims.parse_int "1") in
  let ones = FStar_UInt_UInt16.int_to_uint16 (Prims.parse_int "65535") in  
  let ones' = FStar_UInt_UInt16.sub_mod zero one in
  let zero' = FStar_UInt_UInt16.add_mod ones one in
  let ones_square = FStar_UInt_UInt16.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 65535 65535\nGot:     %s %s %s %s %s %s\n"
                (FStar_UInt_UInt16.to_string zero)
                (FStar_UInt_UInt16.to_string zero')
                (FStar_UInt_UInt16.to_string one)
                (FStar_UInt_UInt16.to_string ones_square)
                (FStar_UInt_UInt16.to_string ones)
                (FStar_UInt_UInt16.to_string ones');
  ()

let test_uint32 () =
  let zero = FStar_UInt_UInt32.int_to_uint32 (Prims.parse_int "0") in
  let one = FStar_UInt_UInt32.int_to_uint32 (Prims.parse_int "1") in
  let ones = FStar_UInt_UInt32.int_to_uint32 (Prims.parse_int "4294967295") in  
  let ones' = FStar_UInt_UInt32.sub_mod zero one in
  let zero' = FStar_UInt_UInt32.add_mod ones one in
  let ones_square = FStar_UInt_UInt32.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 4294967295 4294967295 \nGot:     %s %s %s %s %s %s\n"
                (FStar_UInt_UInt32.to_string zero)
                (FStar_UInt_UInt32.to_string zero')
                (FStar_UInt_UInt32.to_string one)
                (FStar_UInt_UInt32.to_string ones_square)
                (FStar_UInt_UInt32.to_string ones)
                (FStar_UInt_UInt32.to_string ones');
  ()

let test_uint63 () =
  let zero = FStar_UInt_UInt63.int_to_uint63 (Prims.parse_int "0") in
  let one = FStar_UInt_UInt63.int_to_uint63 (Prims.parse_int "1") in
  let ones = FStar_UInt_UInt63.int_to_uint63 (Prims.parse_int "9223372036854775807") in  
  let ones' = FStar_UInt_UInt63.sub_mod zero one in
  let zero' = FStar_UInt_UInt63.add_mod ones one in
  let ones_square = FStar_UInt_UInt63.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 9223372036854775807 9223372036854775807 \nGot:     %s %s %s %s %s %s\n"
                (FStar_UInt_UInt63.to_string zero)
                (FStar_UInt_UInt63.to_string zero')
                (FStar_UInt_UInt63.to_string one)
                (FStar_UInt_UInt63.to_string ones_square)
                (FStar_UInt_UInt63.to_string ones)
                (FStar_UInt_UInt63.to_string ones');
  ()

let test_uint64 () =
  let zero = FStar_UInt_UInt64.int_to_uint64 (Prims.parse_int "0") in
  let one = FStar_UInt_UInt64.int_to_uint64 (Prims.parse_int "1") in
  let ones = FStar_UInt_UInt64.int_to_uint64 (Prims.parse_int "18446744073709551615") in  
  let ones' = FStar_UInt_UInt64.sub_mod zero one in
  let zero' = FStar_UInt_UInt64.add_mod ones one in
  let ones_square = FStar_UInt_UInt64.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 18446744073709551615 18446744073709551615 \nGot:     %s %s %s %s %s %s\n"
                (FStar_UInt_UInt64.to_string zero)
                (FStar_UInt_UInt64.to_string zero')
                (FStar_UInt_UInt64.to_string one)
                (FStar_UInt_UInt64.to_string ones_square)
                (FStar_UInt_UInt64.to_string ones)
                (FStar_UInt_UInt64.to_string ones');
  ()

let test_int8 () =
  let zero = FStar_Int_Int8.int_to_int8 (Prims.parse_int "0") in
  let one = FStar_Int_Int8.int_to_int8 (Prims.parse_int "1") in
  let ones = FStar_Int_Int8.int_to_int8 (Prims.parse_int "-1") in
  let ones' = FStar_Int_Int8.sub_mod zero one in
  let zero' = FStar_Int_Int8.add_mod ones one in
  let ones_square = FStar_Int_Int8.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 -1 -1\nGot:     %s %s %s %s %s %s\n"
                (FStar_Int_Int8.to_string zero)
                (FStar_Int_Int8.to_string zero')
                (FStar_Int_Int8.to_string one)
                (FStar_Int_Int8.to_string ones_square)
                (FStar_Int_Int8.to_string ones)
                (FStar_Int_Int8.to_string ones');
  ()
    
let test_int16 () =
  let zero = FStar_Int_Int16.int_to_int16 (Prims.parse_int "0") in
  let one = FStar_Int_Int16.int_to_int16 (Prims.parse_int "1") in
  let ones = FStar_Int_Int16.int_to_int16 (Prims.parse_int "-1") in
  let ones' = FStar_Int_Int16.sub_mod zero one in
  let zero' = FStar_Int_Int16.add_mod ones one in
  let ones_square = FStar_Int_Int16.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 -1 -1\nGot:     %s %s %s %s %s %s\n"
                (FStar_Int_Int16.to_string zero)
                (FStar_Int_Int16.to_string zero')
                (FStar_Int_Int16.to_string one)
                (FStar_Int_Int16.to_string ones_square)
                (FStar_Int_Int16.to_string ones)
                (FStar_Int_Int16.to_string ones');
  ()
    
let test_int32 () =
  let zero = FStar_Int_Int32.int_to_int32 (Prims.parse_int "0") in
  let one = FStar_Int_Int32.int_to_int32 (Prims.parse_int "1") in
  let ones = FStar_Int_Int32.int_to_int32 (Prims.parse_int "-1") in
  let ones' = FStar_Int_Int32.sub_mod zero one in
  let zero' = FStar_Int_Int32.add_mod ones one in
  let ones_square = FStar_Int_Int32.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 -1 -1\nGot:     %s %s %s %s %s %s\n"
                (FStar_Int_Int32.to_string zero)
                (FStar_Int_Int32.to_string zero')
                (FStar_Int_Int32.to_string one)
                (FStar_Int_Int32.to_string ones_square)
                (FStar_Int_Int32.to_string ones)
                (FStar_Int_Int32.to_string ones');
  ()
    
let test_int63 () =
  let zero = FStar_Int_Int63.int_to_int63 (Prims.parse_int "0") in
  let one = FStar_Int_Int63.int_to_int63 (Prims.parse_int "1") in
  let ones = FStar_Int_Int63.int_to_int63 (Prims.parse_int "-1") in
  let ones' = FStar_Int_Int63.sub_mod zero one in
  let zero' = FStar_Int_Int63.add_mod ones one in
  let ones_square = FStar_Int_Int63.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 -1 -1\nGot:     %s %s %s %s %s %s\n"
                (FStar_Int_Int63.to_string zero)
                (FStar_Int_Int63.to_string zero')
                (FStar_Int_Int63.to_string one)
                (FStar_Int_Int63.to_string ones_square)
                (FStar_Int_Int63.to_string ones)
                (FStar_Int_Int63.to_string ones');
  ()

let test_int64 () =
  let zero = FStar_Int_Int64.int_to_int64 (Prims.parse_int "0") in
  let one = FStar_Int_Int64.int_to_int64 (Prims.parse_int "1") in
  let ones = FStar_Int_Int64.int_to_int64 (Prims.parse_int "-1") in
  let ones' = FStar_Int_Int64.sub_mod zero one in
  let zero' = FStar_Int_Int64.add_mod ones one in
  let ones_square = FStar_Int_Int64.mul_mod ones ones in
  Printf.printf "Expected 0 0 1 1 -1 -1\nGot:     %s %s %s %s %s %s\n"
                (FStar_Int_Int64.to_string zero)
                (FStar_Int_Int64.to_string zero')
                (FStar_Int_Int64.to_string one)
                (FStar_Int_Int64.to_string ones_square)
                (FStar_Int_Int64.to_string ones)
                (FStar_Int_Int64.to_string ones');
  ()
                
let _ =
  test_uint8 ();
  test_uint16 ();
  test_uint32 ();
  test_uint63 ();
  test_uint64 ();
  test_int8 ();
  test_int16 ();
  test_int32 ();
  test_int63 ();
  test_int64 ()
  
              
  
  
