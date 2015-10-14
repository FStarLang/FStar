open AST

open FFI

let const_meta = AST.Meta ([], AST.Can_b, [], AST.Can_w)

let program = E_const (C_unit ())
