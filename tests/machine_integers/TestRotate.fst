module TestRotate

open FStar.All
open FStar.IO

module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I8   = FStar.Int8
module I32  = FStar.Int32

let check s (b:bool) : ML unit =
    if not b then failwith s

(* Test rotate_left for UInt32 *)
let test_u32_rotate_left () : ML unit =
    (* Rotate left by 0 should be identity *)
    check "u32_rol_0"
        (U32.to_string (U32.rotate_left 0x12345678ul 0ul) = "305419896");
    
    (* Rotate left by 4 (one nibble): 0x12345678 -> 0x23456781 *)
    check "u32_rol_4"
        (U32.to_string (U32.rotate_left 0x12345678ul 4ul) = "591751041");
    
    (* Rotate left by 8 (one byte): 0x12345678 -> 0x34567812 *)
    check "u32_rol_8"
        (U32.to_string (U32.rotate_left 0x12345678ul 8ul) = "878082066");
    
    (* Rotate left by 16 (two bytes): 0x12345678 -> 0x56781234 *)
    check "u32_rol_16"
        (U32.to_string (U32.rotate_left 0x12345678ul 16ul) = "1450709556");
    
    (* Rotate left by 1 *)
    check "u32_rol_1_ff"
        (U32.to_string (U32.rotate_left 0xFFFFFFFFul 1ul) = "4294967295");
    
    (* Rotate left by 1 on 1 *)
    check "u32_rol_1_one"
        (U32.to_string (U32.rotate_left 1ul 1ul) = "2");
    
    (* Rotate left by 31 on 1 *)
    check "u32_rol_31_one"
        (U32.to_string (U32.rotate_left 1ul 31ul) = "2147483648");
    ()

(* Test rotate_right for UInt32 *)
let test_u32_rotate_right () : ML unit =
    (* Rotate right by 0 should be identity *)
    check "u32_ror_0"
        (U32.to_string (U32.rotate_right 0x12345678ul 0ul) = "305419896");
    
    (* Rotate right by 4 (one nibble): 0x12345678 -> 0x81234567 *)
    check "u32_ror_4"
        (U32.to_string (U32.rotate_right 0x12345678ul 4ul) = "2166572391");
    
    (* Rotate right by 8 (one byte): 0x12345678 -> 0x78123456 *)
    check "u32_ror_8"
        (U32.to_string (U32.rotate_right 0x12345678ul 8ul) = "2014458966");
    
    (* Rotate right by 16 (two bytes): 0x12345678 -> 0x56781234 *)
    check "u32_ror_16"
        (U32.to_string (U32.rotate_right 0x12345678ul 16ul) = "1450709556");
    
    (* Rotate right by 1 on all ones *)
    check "u32_ror_1_ff"
        (U32.to_string (U32.rotate_right 0xFFFFFFFFul 1ul) = "4294967295");
    
    (* Rotate right by 1 on 1 should give high bit *)
    check "u32_ror_1_one"
        (U32.to_string (U32.rotate_right 1ul 1ul) = "2147483648");
    ()

(* Test rotate_left for UInt8 *)
let test_u8_rotate_left () : ML unit =
    (* Rotate left by 0 should be identity *)
    check "u8_rol_0"
        (U8.to_string (U8.rotate_left 0x12uy 0ul) = "18");
    
    (* Rotate left by 4 (one nibble): 0x12 -> 0x21 *)
    check "u8_rol_4"
        (U8.to_string (U8.rotate_left 0x12uy 4ul) = "33");
    
    (* Rotate left by 1 on all ones *)
    check "u8_rol_1_ff"
        (U8.to_string (U8.rotate_left 0xFFuy 1ul) = "255");
    
    (* Rotate left by 1 on 1 *)
    check "u8_rol_1_one"
        (U8.to_string (U8.rotate_left 1uy 1ul) = "2");
    
    (* Rotate left by 7 on 1 *)
    check "u8_rol_7_one"
        (U8.to_string (U8.rotate_left 1uy 7ul) = "128");
    ()

(* Test rotate_right for UInt8 *)
let test_u8_rotate_right () : ML unit =
    (* Rotate right by 0 should be identity *)
    check "u8_ror_0"
        (U8.to_string (U8.rotate_right 0x12uy 0ul) = "18");
    
    (* Rotate right by 4 (one nibble): 0x12 -> 0x21 *)
    check "u8_ror_4"
        (U8.to_string (U8.rotate_right 0x12uy 4ul) = "33");
    
    (* Rotate right by 1 on 1 *)
    check "u8_ror_1_one"
        (U8.to_string (U8.rotate_right 1uy 1ul) = "128");
    ()

(* Test rotate_left for UInt64 *)
let test_u64_rotate_left () : ML unit =
    (* Rotate left by 0 should be identity *)
    check "u64_rol_0"
        (U64.to_string (U64.rotate_left 0x123456789ABCDEFuL 0ul) = "81985529216486895");
    
    (* Rotate left by 4: 0x0123456789ABCDEF -> 0x123456789ABCDEF0 *)
    check "u64_rol_4"
        (U64.to_string (U64.rotate_left 0x123456789ABCDEFuL 4ul) = "1311768467463790320");
    
    (* Rotate left by 1 on 1 *)
    check "u64_rol_1_one"
        (U64.to_string (U64.rotate_left 1uL 1ul) = "2");
    
    (* Rotate left by 63 on 1 *)
    check "u64_rol_63_one"
        (U64.to_string (U64.rotate_left 1uL 63ul) = "9223372036854775808");
    ()

(* Test rotate_right for UInt64 *)
let test_u64_rotate_right () : ML unit =
    (* Rotate right by 0 should be identity *)
    check "u64_ror_0"
        (U64.to_string (U64.rotate_right 0x123456789ABCDEFuL 0ul) = "81985529216486895");
    
    (* Rotate right by 1 on 1 *)
    check "u64_ror_1_one"
        (U64.to_string (U64.rotate_right 1uL 1ul) = "9223372036854775808");
    ()

(* Test inverse property: rotate_right(rotate_left(x, s), s) = x *)
let test_inverse_u32 () : ML unit =
    let x = 0x12345678ul in
    check "u32_inverse_4"
        (U32.rotate_right (U32.rotate_left x 4ul) 4ul = x);
    check "u32_inverse_8"
        (U32.rotate_right (U32.rotate_left x 8ul) 8ul = x);
    check "u32_inverse_16"
        (U32.rotate_right (U32.rotate_left x 16ul) 16ul = x);
    check "u32_inverse_1"
        (U32.rotate_right (U32.rotate_left x 1ul) 1ul = x);
    check "u32_inverse_31"
        (U32.rotate_right (U32.rotate_left x 31ul) 31ul = x);
    ()

(* Test inverse property the other way: rotate_left(rotate_right(x, s), s) = x *)
let test_inverse_u32_other () : ML unit =
    let x = 0x12345678ul in
    check "u32_inverse_other_4"
        (U32.rotate_left (U32.rotate_right x 4ul) 4ul = x);
    check "u32_inverse_other_8"
        (U32.rotate_left (U32.rotate_right x 8ul) 8ul = x);
    check "u32_inverse_other_16"
        (U32.rotate_left (U32.rotate_right x 16ul) 16ul = x);
    ()

(* Test signed Int32 rotate (non-negative values only) *)
let test_i32_rotate () : ML unit =
    check "i32_rol_0"
        (I32.to_string (I32.rotate_left 0x12345678l 0ul) = "305419896");
    check "i32_rol_4"
        (I32.to_string (I32.rotate_left 0x12345678l 4ul) = "591751041");
    check "i32_ror_0"
        (I32.to_string (I32.rotate_right 0x12345678l 0ul) = "305419896");
    ()

let main () : ML int =
    test_u32_rotate_left ();
    test_u32_rotate_right ();
    test_u8_rotate_left ();
    test_u8_rotate_right ();
    test_u64_rotate_left ();
    test_u64_rotate_right ();
    test_inverse_u32 ();
    test_inverse_u32_other ();
    test_i32_rotate ();
    print_string "correct\n";
    0

let _ = main ()
