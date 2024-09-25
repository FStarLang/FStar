use ocaml_interop::{
    impl_from_ocaml_record, impl_from_ocaml_variant, ocaml_export, OCaml, OCamlList, OCamlRef,
    ToOCaml,
};
use proc_macro2::Span;
use syn::{
    punctuated::Punctuated, token::Brace, token::Colon, token::Comma, token::Eq, token::Let,
    token::Mut, token::Paren, token::Pub, token::RArrow, token::Ref, token::Semi, Block, Generics,
    Ident, ItemFn, Local, LocalInit, Pat as SynPat, PatType, Path, PathArguments, ReturnType,
    Signature, Type, Visibility,
};

use std::fmt;
use std::str::FromStr;

enum LitIntWidth {
    I8,
    I16,
    I32,
    I64,
}

#[allow(dead_code)]
struct LitInt {
    lit_int_val: String,
    lit_int_signed: Option<bool>,
    lit_int_width: Option<LitIntWidth>,
}

enum Lit {
    LitInt(LitInt),
    LitBool(bool),
    LitUnit,
    LitString(String),
}

enum BinOp {
    Add,
    Sub,
    Ne,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Rem,
    And,
    Or,
    Mul,
    Shr,
    Shl,
    BitAnd,
    BitOr,
}

enum UnOp {
    Deref,
}

struct ExprCall {
    call_fn: Box<Expr>,
    call_args: Vec<Expr>,
}

struct ExprBin {
    expr_bin_left: Box<Expr>,
    op: BinOp,
    expr_bin_right: Box<Expr>,
}

struct ExprUnary {
    expr_unary_op: UnOp,
    expr_unary_expr: Box<Expr>,
}

struct ExprAssign {
    expr_assign_l: Box<Expr>,
    expr_assign_r: Box<Expr>,
}

struct ExprIf {
    expr_if_cond: Box<Expr>,
    expr_if_then: Vec<Stmt>,
    expr_if_else: Option<Box<Expr>>,
}

struct ExprWhile {
    expr_while_cond: Box<Expr>,
    expr_while_body: Vec<Stmt>,
}

struct ExprIndex {
    expr_index_base: Box<Expr>,
    expr_index_index: Box<Expr>,
}

struct ExprRepeat {
    expr_repeat_elem: Box<Expr>,
    expr_repeat_len: Box<Expr>,
}

struct ExprReference {
    expr_reference_is_mut: bool,
    expr_reference_expr: Box<Expr>,
}

struct Arm {
    arm_pat: Box<Pat>,
    arm_body: Box<Expr>,
}

struct ExprMatch {
    expr_match_expr: Box<Expr>,
    expr_match_arms: Vec<Arm>,
}

struct ExprField {
    expr_field_base: Box<Expr>,
    expr_field_name: String,
    expr_field_named: bool,
}

struct FieldVal {
    field_val_name: String,
    field_val_expr: Box<Expr>,
}

struct ExprStruct {
    expr_struct_path: Vec<String>,
    expr_struct_fields: Vec<FieldVal>,
}

struct ExprMethodCall {
    expr_method_call_receiver: Box<Expr>,
    expr_method_call_name: String,
    expr_method_call_args: Vec<Expr>,
}

struct ExprCast {
    expr_cast_expr: Box<Expr>,
    expr_cast_type: Box<Typ>,
}

enum Expr {
    EBinOp(ExprBin),
    EPath(Vec<PathSegment>),
    ECall(ExprCall),
    EUnOp(ExprUnary),
    EAssign(ExprAssign),
    EBlock(Vec<Stmt>),
    ELit(Lit),
    EIf(ExprIf),
    EWhile(ExprWhile),
    EIndex(ExprIndex),
    ERepeat(ExprRepeat),
    EReference(ExprReference),
    EMatch(ExprMatch),
    EField(ExprField),
    EStruct(ExprStruct),
    ETuple(Vec<Expr>),
    EMethodCall(ExprMethodCall),
    ECast(ExprCast),
}

struct TypeReference {
    type_reference_mut: bool,
    type_reference_typ: Box<Typ>,
}

struct PathSegment {
    path_segment_name: String,
    path_segment_generic_args: Vec<Typ>,
}

struct TypeArray {
    type_array_elem: Box<Typ>,
    type_array_len: Expr,
}

struct TypeFn {
    type_fn_args: Vec<Typ>,
    type_fn_ret: Box<Typ>,
}

enum Typ {
    TPath(Vec<PathSegment>),
    TReference(TypeReference),
    TSlice(Box<Typ>),
    TArray(TypeArray),
    TUnit,
    TInfer,
    TFn(TypeFn),
    TTuple(Vec<Typ>),
}

struct PatIdent {
    pat_name: String,
    by_ref: bool,
    is_mut: bool,
}

struct PatTupleStruct {
    pat_ts_path: Vec<PathSegment>,
    pat_ts_elems: Vec<Pat>,
}

struct FieldPat {
    field_pat_name: String,
    field_pat_pat: Box<Pat>,
}

struct PatStruct {
    pat_struct_path: String,
    pat_struct_fields: Vec<FieldPat>,
}

enum Pat {
    PIdent(PatIdent),
    PTupleStruct(PatTupleStruct),
    PWild,
    PLit(Lit),
    PStruct(PatStruct),
    PTuple(Vec<Pat>),
    PTyp(Box<PatTyp>),
    PPath(Vec<PathSegment>),
}

struct LocalStmt {
    local_stmt_pat: Option<Pat>,
    local_stmt_init: Option<Expr>,
}

enum Stmt {
    SLocal(LocalStmt),
    SExpr(Expr),
}

struct GenericTypeParam {
    generic_type_param_name: String,
    generic_type_param_trait_bounds: Vec<Vec<String>>,
}

enum GenericParam {
    GenTypeParam(GenericTypeParam),
}

struct PatTyp {
    pat_typ_pat: Pat,
    pat_typ_typ: Typ,
}

enum FnArg {
    FnArgPat(PatTyp),
}

struct FnSig {
    fn_const: bool,
    fn_name: String,
    fn_generics: Vec<GenericParam>,
    fn_args: Vec<FnArg>,
    fn_ret_t: Typ,
}

struct Fn {
    fn_sig: FnSig,
    fn_body: Vec<Stmt>,
}

struct FieldTyp {
    field_typ_name: String,
    field_typ_typ: Typ,
}

enum Attribute {
    AttrDerive(String),
}

struct ItemStruct {
    item_struct_attrs: Vec<Attribute>,
    item_struct_name: String,
    item_struct_generics: Vec<GenericParam>,
    item_struct_fields: Vec<FieldTyp>,
}

struct ItemType {
    item_type_name: String,
    item_type_generics: Vec<GenericParam>,
    item_type_typ: Typ,
}

struct EnumVariant {
    enum_variant_name: String,
    enum_variant_fields: Vec<Typ>,
}

struct ItemEnum {
    item_enum_attrs: Vec<Attribute>,
    item_enum_name: String,
    item_enum_generics: Vec<GenericParam>,
    item_enum_variants: Vec<EnumVariant>,
}

struct ItemStatic {
    item_static_name: String,
    item_static_typ: Typ,
    item_static_init: Expr,
}

enum Item {
    IFn(Fn),
    IStruct(ItemStruct),
    IType(ItemType),
    IEnum(ItemEnum),
    IStatic(ItemStatic),
}

#[allow(dead_code)]
struct File {
    file_name: String,
    file_items: Vec<Item>,
}

const VEC_NEW_FN: &str = "vec_new";
const PANIC_FN: &str = "panic";

fn fn_to_string(f: &Fn) -> String {
    f.to_string()
}

impl_from_ocaml_variant! {
  LitIntWidth {
      LitIntWidth::I8,
      LitIntWidth::I16,
      LitIntWidth::I32,
      LitIntWidth::I64,
  }
}

impl_from_ocaml_record! {
  LitInt {
    lit_int_val : String,
    lit_int_signed : Option<bool>,
    lit_int_width : Option<LitIntWidth>,
  }
}

impl_from_ocaml_variant! {
  Lit {
    Lit::LitInt (payload:LitInt),
    Lit::LitBool (payload:bool),
    Lit::LitUnit,
    Lit::LitString (payload:String),
  }
}

impl_from_ocaml_variant! {
  BinOp {
      BinOp::Add,
      BinOp::Sub,
      BinOp::Ne,
      BinOp::Eq,
      BinOp::Lt,
      BinOp::Le,
      BinOp::Gt,
      BinOp::Ge,
      BinOp::Rem,
      BinOp::And,
      BinOp::Or,
      BinOp::Mul,
      BinOp::Shr,
      BinOp::Shl,
      BinOp::BitAnd,
      BinOp::BitOr,
  }
}

impl_from_ocaml_variant! {
  UnOp {
      UnOp::Deref,
  }
}

impl_from_ocaml_variant! {
  Expr {
    Expr::EBinOp (payload:ExprBin),
    Expr::EPath (payload:OCamlList<PathSegment>),
    Expr::ECall (payload:ExprCall),
    Expr::EUnOp (payload:ExprUnary),
    Expr::EAssign (payload:ExprAssign),
    Expr::EBlock (payload:OCamlList<Stmt>),
    Expr::ELit (payload:Lit),
    Expr::EIf (payload:ExprIf),
    Expr::EWhile (payload:ExprWhile),
    Expr::EIndex (payload:ExprIndex),
    Expr::ERepeat (payload:ExprRepeat),
    Expr::EReference (payload:ExprReference),
    Expr::EMatch (payload:ExprMatch),
    Expr::EField (payload:ExprField),
    Expr::EStruct (payload:ExprStruct),
    Expr::ETuple (payload:OCamlList<Expr>),
    Expr::EMethodCall (payload:ExprMethodCall),
    Expr::ECast (payload:ExprCast),
  }
}

impl_from_ocaml_record! {
  ExprCall {
    call_fn: Expr,
    call_args: OCamlList<Expr>
  }
}

impl_from_ocaml_record! {
  ExprBin {
    expr_bin_left: Expr,
    op: BinOp,
    expr_bin_right: Expr,
  }
}

impl_from_ocaml_record! {
  ExprUnary {
    expr_unary_op: UnOp,
    expr_unary_expr: Expr,
  }
}

impl_from_ocaml_record! {
  ExprAssign {
    expr_assign_l: Expr,
    expr_assign_r: Expr,
  }
}

impl_from_ocaml_record! {
  ExprIf {
    expr_if_cond: Expr,
    expr_if_then: OCamlList<Stmt>,
    expr_if_else: Option<Expr>
  }
}

impl_from_ocaml_record! {
  ExprWhile {
    expr_while_cond: Expr,
    expr_while_body: OCamlList<Stmt>,
  }
}

impl_from_ocaml_record! {
  ExprIndex {
    expr_index_base: Expr,
    expr_index_index: Expr,
  }
}

impl_from_ocaml_record! {
  ExprRepeat {
    expr_repeat_elem: Expr,
    expr_repeat_len: Expr,
  }
}

impl_from_ocaml_record! {
  ExprReference {
    expr_reference_is_mut: bool,
    expr_reference_expr: Expr,
  }
}

impl_from_ocaml_record! {
  Arm {
    arm_pat: Pat,
    arm_body: Expr,
  }
}

impl_from_ocaml_record! {
  ExprMatch {
    expr_match_expr: Expr,
    expr_match_arms: OCamlList<Arm>,
  }
}

impl_from_ocaml_record! {
  ExprField {
    expr_field_base: Expr,
    expr_field_name: String,
    expr_field_named: bool,
  }
}

impl_from_ocaml_record! {
  FieldVal {
    field_val_name: String,
    field_val_expr: Expr,
  }
}

impl_from_ocaml_record! {
  ExprStruct {
    expr_struct_path: OCamlList<String>,
    expr_struct_fields: OCamlList<FieldVal>,
  }
}

impl_from_ocaml_record! {
  ExprMethodCall {
    expr_method_call_receiver: Expr,
    expr_method_call_name: String,
    expr_method_call_args: OCamlList<Expr>,
  }
}

impl_from_ocaml_record! {
  ExprCast {
    expr_cast_expr: Expr,
    expr_cast_type: Typ,
  }
}

impl_from_ocaml_record! {
  TypeReference {
    type_reference_mut: bool,
    type_reference_typ: Typ,
  }
}

impl_from_ocaml_record! {
  PathSegment {
    path_segment_name: String,
    path_segment_generic_args: OCamlList<Typ>,
  }
}

impl_from_ocaml_record! {
  TypeArray {
    type_array_elem: Typ,
    type_array_len: Expr,
  }
}

impl_from_ocaml_record! {
  TypeFn {
    type_fn_args: OCamlList<Typ>,
    type_fn_ret: Typ,
  }
}

impl_from_ocaml_variant! {
  Typ {
    Typ::TPath (payload:OCamlList<PathSegment>),
    Typ::TReference (payload:TypeReference),
    Typ::TSlice (payload:Typ),
    Typ::TArray (payload:TypeArray),
    Typ::TUnit,
    Typ::TInfer,
    Typ::TFn (payload:TypeFn),
    Typ::TTuple (payload:OCamlList<Typ>),
  }
}

impl_from_ocaml_record! {
  PatIdent {
    pat_name : String,
    by_ref : bool,
    is_mut : bool,
  }
}

impl_from_ocaml_record! {
  PatTupleStruct {
    pat_ts_path : OCamlList<PathSegment>,
    pat_ts_elems : OCamlList<Pat>,
  }
}

impl_from_ocaml_record! {
  FieldPat {
    field_pat_name : String,
    field_pat_pat : Pat,
  }
}

impl_from_ocaml_record! {
  PatStruct {
    pat_struct_path : String,
    pat_struct_fields : OCamlList<FieldPat>,
  }
}

impl_from_ocaml_variant! {
  Pat {
    Pat::PIdent (payload:PatIdent),
    Pat::PTupleStruct (payload:PatTupleStruct),
    Pat::PWild,
    Pat::PLit (payload:Lit),
    Pat::PStruct (payload:PatStruct),
    Pat::PTuple (payload:OCamlList<Pat>),
    Pat::PTyp (payload:PatTyp),
    Pat::PPath (payload:OCamlList<PathSegment>),
  }
}

impl_from_ocaml_record! {
  LocalStmt {
    local_stmt_pat : Option<Pat>,
    local_stmt_init : Option<Expr>,
  }
}

impl_from_ocaml_variant! {
  Stmt {
    Stmt::SLocal (payload:LocalStmt),
    Stmt::SExpr (payload:Expr),
  }
}

impl_from_ocaml_record! {
  GenericTypeParam {
    generic_type_param_name : String,
    generic_type_param_trait_bounds : OCamlList<OCamlList<String>>,
  }
}

impl_from_ocaml_variant! {
  GenericParam {
    GenericParam::GenTypeParam (payload:GenericTypeParam),
  }
}

impl_from_ocaml_record! {
  PatTyp {
    pat_typ_pat : Pat,
    pat_typ_typ : Typ,
  }
}

impl_from_ocaml_variant! {
  FnArg {
    FnArg::FnArgPat (payload:PatTyp),
  }
}

impl_from_ocaml_record! {
  FnSig {
    fn_const: bool,
    fn_name : String,
    fn_generics: OCamlList<GenericParam>,
    fn_args : OCamlList<FnArg>,
    fn_ret_t : Typ,
  }
}

impl_from_ocaml_record! {
  Fn {
    fn_sig : FnSig,
    fn_body : OCamlList<Stmt>,
  }
}

impl_from_ocaml_record! {
  FieldTyp {
    field_typ_name : String,
    field_typ_typ : Typ,
  }
}

impl_from_ocaml_variant! {
  Attribute {
    Attribute::AttrDerive (payload:String),
  }
}

impl_from_ocaml_record! {
  ItemStruct {
    item_struct_attrs : OCamlList<Attribute>,
    item_struct_name : String,
    item_struct_generics : OCamlList<GenericParam>,
    item_struct_fields : OCamlList<FieldTyp>,
  }
}

impl_from_ocaml_record! {
  ItemType {
    item_type_name : String,
    item_type_generics : OCamlList<GenericParam>,
    item_type_typ : Typ,
  }
}

impl_from_ocaml_record! {
  EnumVariant {
    enum_variant_name : String,
    enum_variant_fields : OCamlList<Typ>,
  }
}

impl_from_ocaml_record! {
  ItemEnum {
    item_enum_attrs: OCamlList<Attribute>,
    item_enum_name : String,
    item_enum_generics : OCamlList<GenericParam>,
    item_enum_variants : OCamlList<EnumVariant>,
  }
}

impl_from_ocaml_record! {
  ItemStatic {
    item_static_name : String,
    item_static_typ : Typ,
    item_static_init : Expr,
  }
}

impl_from_ocaml_variant! {
  Item {
    Item::IFn (payload:Fn),
    Item::IStruct (payload:ItemStruct),
    Item::IType (payload:ItemType),
    Item::IEnum (payload:ItemEnum),
    Item::IStatic (payload:ItemStatic),
  }
}

impl_from_ocaml_record! {
  File {
    file_name: String,
    file_items : OCamlList<Item>,
  }
}

fn to_syn_path_string(s: &Vec<String>) -> syn::Path {
    let mut segs: Punctuated<syn::PathSegment, syn::token::PathSep> = Punctuated::new();
    s.iter().for_each(|s| {
        segs.push(syn::PathSegment {
            ident: Ident::new(&s, Span::call_site()),
            arguments: PathArguments::None,
        })
    });
    Path {
        leading_colon: None,
        segments: segs,
    }
}

fn to_syn_path(s: &Vec<PathSegment>) -> syn::Path {
    let mut segs: Punctuated<syn::PathSegment, syn::token::PathSep> = Punctuated::new();
    s.iter().for_each(|s| {
        segs.push(syn::PathSegment {
            ident: Ident::new(&s.path_segment_name, Span::call_site()),
            arguments: if s.path_segment_generic_args.len() == 0 {
                PathArguments::None
            } else {
                let mut args: Punctuated<syn::GenericArgument, Comma> = Punctuated::new();
                s.path_segment_generic_args
                    .iter()
                    .for_each(|a| args.push(syn::GenericArgument::Type(to_syn_typ(a))));
                PathArguments::AngleBracketed(syn::AngleBracketedGenericArguments {
                    colon2_token: None,
                    lt_token: syn::token::Lt {
                        spans: [Span::call_site()],
                    },
                    args,
                    gt_token: syn::token::Gt {
                        spans: [Span::call_site()],
                    },
                })
            },
        })
    });
    Path {
        leading_colon: None,
        segments: segs,
    }
}

fn to_syn_binop(op: &BinOp) -> syn::BinOp {
    match op {
        BinOp::Add => syn::BinOp::Add(syn::token::Plus {
            spans: [Span::call_site()],
        }),
        BinOp::Sub => syn::BinOp::Sub(syn::token::Minus {
            spans: [Span::call_site()],
        }),
        BinOp::Ne => syn::BinOp::Ne(syn::token::Ne {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Eq => syn::BinOp::Eq(syn::token::EqEq {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Lt => syn::BinOp::Lt(syn::token::Lt {
            spans: [Span::call_site()],
        }),
        BinOp::Le => syn::BinOp::Le(syn::token::Le {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Gt => syn::BinOp::Gt(syn::token::Gt {
            spans: [Span::call_site()],
        }),
        BinOp::Ge => syn::BinOp::Ge(syn::token::Ge {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Rem => syn::BinOp::Rem(syn::token::Percent {
            spans: [Span::call_site()],
        }),
        BinOp::And => syn::BinOp::And(syn::token::AndAnd {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Or => syn::BinOp::Or(syn::token::OrOr {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Mul => syn::BinOp::Mul(syn::token::Star {
            spans: [Span::call_site()],
        }),
        BinOp::Shr => syn::BinOp::Shr(syn::token::Shr {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::Shl => syn::BinOp::Shl(syn::token::Shl {
            spans: [Span::call_site(), Span::call_site()],
        }),
        BinOp::BitAnd => syn::BinOp::BitAnd(syn::token::And {
            spans: [Span::call_site()],
        }),
        BinOp::BitOr => syn::BinOp::BitOr(syn::token::Or {
            spans: [Span::call_site()],
        }),
    }
}

fn is_vec_new(e: &Expr) -> bool {
    match e {
        Expr::EPath(s) => s[0].path_segment_name == VEC_NEW_FN,
        _ => false,
    }
}

fn is_panic(e: &Expr) -> bool {
    match e {
        Expr::EPath(s) => s[0].path_segment_name == PANIC_FN,
        _ => false,
    }
}

fn to_syn_vec_new(args: &Vec<Expr>) -> syn::Expr {
    let init = to_syn_expr(&args[0]);
    let len = to_syn_expr(&args[1]);
    let init_str = quote::quote!(#init).to_string();
    let len_str = quote::quote!(#len).to_string();
    let macro_args = format!("{}; {}", init_str, len_str);
    let ts = proc_macro2::TokenStream::from_str(&macro_args).unwrap();
    syn::Expr::Macro(syn::ExprMacro {
        attrs: vec![],
        mac: syn::Macro {
            path: to_syn_path(&vec![PathSegment {
                path_segment_name: "vec".to_string(),
                path_segment_generic_args: vec![],
            }]),
            bang_token: syn::token::Not {
                spans: [Span::call_site()],
            },
            delimiter: syn::MacroDelimiter::Bracket(syn::token::Bracket {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            }),
            tokens: ts,
        },
    })
}

fn to_syn_panic() -> syn::Expr {
    let macro_args = "";
    let ts = proc_macro2::TokenStream::from_str(&macro_args).unwrap();
    syn::Expr::Macro(syn::ExprMacro {
        attrs: vec![],
        mac: syn::Macro {
            path: to_syn_path(&vec![PathSegment {
                path_segment_name: "panic".to_string(),
                path_segment_generic_args: vec![],
            }]),
            bang_token: syn::token::Not {
                spans: [Span::call_site()],
            },
            delimiter: syn::MacroDelimiter::Paren(syn::token::Paren {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            }),
            tokens: ts,
        },
    })
}

fn to_syn_arm(e: &Arm) -> syn::Arm {
    syn::Arm {
        attrs: vec![],
        pat: to_syn_pat(&e.arm_pat),
        guard: None,
        fat_arrow_token: syn::token::FatArrow {
            spans: [Span::call_site(), Span::call_site()],
        },
        body: Box::new(to_syn_expr(&e.arm_body)),
        comma: Some(syn::token::Comma {
            spans: [Span::call_site()],
        }),
    }
}

fn to_syn_lit(e: &Lit) -> syn::Lit {
    match e {
        Lit::LitInt(LitInt { lit_int_val, .. }) => {
            syn::Lit::Int(syn::LitInt::new(lit_int_val, Span::call_site()))
        }
        Lit::LitBool(b) => syn::Lit::Bool(syn::LitBool {
            value: *b,
            span: Span::call_site(),
        }),
        Lit::LitUnit => panic!("Don't know how to translate LitUnit"),
        Lit::LitString(s) => syn::Lit::Str(syn::LitStr::new(s, Span::call_site())),
    }
}

fn to_syn_expr(e: &Expr) -> syn::Expr {
    match e {
        Expr::EBinOp(e) => {
            let e1 = to_syn_expr(&e.expr_bin_left);
            let e2 = to_syn_expr(&e.expr_bin_right);
            syn::Expr::Binary(syn::ExprBinary {
                attrs: vec![],
                left: Box::new(e1),
                op: to_syn_binop(&e.op),
                right: Box::new(e2),
            })
        }
        Expr::EPath(s) => {
            let path = to_syn_path(s);
            syn::Expr::Path(syn::ExprPath {
                attrs: vec![],
                qself: None,
                path,
            })
        }
        Expr::ECall(e) => {
            if is_vec_new(&e.call_fn) {
                to_syn_vec_new(&e.call_args)
            } else if is_panic(&e.call_fn) {
                to_syn_panic()
            } else {
                let mut args: Punctuated<syn::Expr, Comma> = Punctuated::new();
                e.call_args.iter().for_each(|a| args.push(to_syn_expr(a)));
                let func = Box::new(to_syn_expr(&e.call_fn));
                syn::Expr::Call(syn::ExprCall {
                    attrs: vec![],
                    func,
                    paren_token: Paren::default(),
                    args,
                })
            }
        }
        Expr::EUnOp(e) => {
            let e1 = to_syn_expr(&e.expr_unary_expr);
            syn::Expr::Unary(syn::ExprUnary {
                attrs: vec![],
                op: match e.expr_unary_op {
                    UnOp::Deref => syn::UnOp::Deref(syn::token::Star {
                        spans: [Span::call_site()],
                    }),
                },
                expr: Box::new(e1),
            })
        }
        Expr::EAssign(e) => {
            let e1 = to_syn_expr(&e.expr_assign_l);
            let e2 = to_syn_expr(&e.expr_assign_r);
            syn::Expr::Assign(syn::ExprAssign {
                attrs: vec![],
                left: Box::new(e1),
                eq_token: Eq {
                    spans: [Span::call_site()],
                },
                right: Box::new(e2),
            })
        }
        Expr::EBlock(stmts) => {
            let stmts = stmts.iter().map(to_syn_stmt).collect();
            syn::Expr::Block(syn::ExprBlock {
                attrs: vec![],
                label: None,
                block: Block {
                    brace_token: Brace::default(),
                    stmts,
                },
            })
        }
        Expr::ELit(lit) => match lit {
            Lit::LitUnit => syn::Expr::Tuple(syn::ExprTuple {
                attrs: vec![],
                paren_token: Paren::default(),
                elems: Punctuated::new(),
            }),
            _ => syn::Expr::Lit(syn::ExprLit {
                attrs: vec![],
                lit: to_syn_lit(lit),
            }),
        },
        Expr::EIf(ExprIf {
            expr_if_cond,
            expr_if_then,
            expr_if_else,
        }) => {
            let cond: Box<syn::Expr> = Box::new(to_syn_expr(expr_if_cond));
            let if_then: Block = Block {
                brace_token: Brace::default(),
                stmts: expr_if_then.iter().map(to_syn_stmt).collect(),
            };
            let if_else: Option<(syn::token::Else, Box<syn::Expr>)> = match expr_if_else {
                None => None,
                Some(e) => Some((
                    syn::token::Else {
                        span: Span::call_site(),
                    },
                    Box::new(to_syn_expr(e)),
                )),
            };
            syn::Expr::If(syn::ExprIf {
                attrs: vec![],
                if_token: syn::token::If {
                    span: Span::call_site(),
                },
                cond,
                then_branch: if_then,
                else_branch: if_else,
            })
        }
        Expr::EWhile(ExprWhile {
            expr_while_cond,
            expr_while_body,
        }) => {
            let cond: Box<syn::Expr> = Box::new(to_syn_expr(expr_while_cond));
            let body: Block = Block {
                brace_token: Brace::default(),
                stmts: expr_while_body.iter().map(to_syn_stmt).collect(),
            };
            syn::Expr::While(syn::ExprWhile {
                attrs: vec![],
                label: None,
                while_token: syn::token::While {
                    span: Span::call_site(),
                },
                cond,
                body,
            })
        }
        Expr::EIndex(ExprIndex {
            expr_index_base,
            expr_index_index,
        }) => syn::Expr::Index({
            syn::ExprIndex {
                attrs: vec![],
                expr: Box::new(to_syn_expr(expr_index_base)),
                bracket_token: syn::token::Bracket {
                    span: proc_macro2::Group::new(
                        proc_macro2::Delimiter::None,
                        proc_macro2::TokenStream::new(),
                    )
                    .delim_span(),
                },
                index: Box::new(to_syn_expr(expr_index_index)),
            }
        }),
        Expr::ERepeat(ExprRepeat {
            expr_repeat_elem,
            expr_repeat_len,
        }) => syn::Expr::Repeat(syn::ExprRepeat {
            attrs: vec![],
            bracket_token: syn::token::Bracket {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            },
            expr: Box::new(to_syn_expr(expr_repeat_elem)),
            semi_token: syn::token::Semi {
                spans: [Span::call_site()],
            },
            len: Box::new(to_syn_expr(expr_repeat_len)),
        }),
        Expr::EReference(ExprReference {
            expr_reference_is_mut,
            expr_reference_expr,
        }) => syn::Expr::Reference(syn::ExprReference {
            attrs: vec![],
            and_token: syn::token::And {
                spans: [Span::call_site()],
            },
            mutability: if *expr_reference_is_mut {
                Some(syn::token::Mut {
                    span: Span::call_site(),
                })
            } else {
                None
            },
            expr: Box::new(to_syn_expr(expr_reference_expr)),
        }),
        Expr::EMatch(ExprMatch {
            expr_match_expr,
            expr_match_arms,
        }) => syn::Expr::Match(syn::ExprMatch {
            attrs: vec![],
            match_token: syn::token::Match {
                span: Span::call_site(),
            },
            expr: Box::new(to_syn_expr(expr_match_expr)),
            brace_token: Brace::default(),
            arms: expr_match_arms.iter().map(to_syn_arm).collect(),
        }),
        Expr::EField(ExprField {
            expr_field_base,
            expr_field_name,
            expr_field_named,
        }) => syn::Expr::Field(syn::ExprField {
            attrs: vec![],
            base: Box::new(to_syn_expr(expr_field_base)),
            dot_token: syn::token::Dot {
                spans: [Span::call_site()],
            },
            member: if *expr_field_named {
                syn::Member::Named(Ident::new(expr_field_name, Span::call_site()))
            } else {
                syn::Member::Unnamed(syn::Index {
                    index: expr_field_name.parse::<u32>().unwrap(),
                    span: Span::call_site(),
                })
            },
        }),
        Expr::EStruct(ExprStruct {
            expr_struct_path,
            expr_struct_fields,
        }) => {
            let mut fields: Punctuated<syn::FieldValue, Comma> = Punctuated::new();
            expr_struct_fields.iter().for_each(|f| {
                fields.push(syn::FieldValue {
                    attrs: vec![],
                    member: syn::Member::Named(Ident::new(&f.field_val_name, Span::call_site())),
                    colon_token: Some(Colon {
                        spans: [Span::call_site()],
                    }),
                    expr: to_syn_expr(&f.field_val_expr),
                })
            });
            syn::Expr::Struct(syn::ExprStruct {
                attrs: vec![],
                qself: None,
                path: to_syn_path_string(expr_struct_path),
                brace_token: Brace::default(),
                fields,
                dot2_token: None,
                rest: None,
            })
        }
        Expr::ETuple(es) => syn::Expr::Tuple(syn::ExprTuple {
            attrs: vec![],
            paren_token: Paren::default(),
            elems: {
                let mut exprs: Punctuated<syn::Expr, Comma> = Punctuated::new();
                es.iter().for_each(|e| exprs.push(to_syn_expr(e)));
                exprs
            },
        }),
        Expr::EMethodCall(ExprMethodCall {
            expr_method_call_receiver,
            expr_method_call_name,
            expr_method_call_args,
        }) => {
            let mut args: Punctuated<syn::Expr, Comma> = Punctuated::new();
            expr_method_call_args
                .iter()
                .for_each(|a| args.push(to_syn_expr(a)));
            syn::Expr::MethodCall(syn::ExprMethodCall {
                attrs: vec![],
                receiver: Box::new(to_syn_expr(expr_method_call_receiver)),
                dot_token: syn::token::Dot {
                    spans: [Span::call_site()],
                },
                method: Ident::new(&expr_method_call_name, Span::call_site()),
                turbofish: None,
                paren_token: Paren::default(),
                args,
            })
        },
        Expr::ECast(ExprCast { expr_cast_expr, expr_cast_type }) => {
            syn::Expr::Cast(syn::ExprCast {
                attrs: vec![],
                expr: Box::new(to_syn_expr(expr_cast_expr)),
                as_token: syn::token::As { span: Span::call_site() },
                ty: Box::new(to_syn_typ(expr_cast_type)),
            })
        },
    }
}

fn to_syn_pat(p: &Pat) -> syn::Pat {
    match p {
        Pat::PIdent(p) => SynPat::Ident(syn::PatIdent {
            attrs: vec![],
            by_ref: if p.by_ref {
                Some(Ref {
                    span: Span::call_site(),
                })
            } else {
                None
            },
            mutability: if p.is_mut {
                Some(Mut {
                    span: Span::call_site(),
                })
            } else {
                None
            },
            ident: Ident::new(&p.pat_name, Span::call_site()),
            subpat: None,
        }),
        Pat::PTupleStruct(pts) => SynPat::TupleStruct(syn::PatTupleStruct {
            attrs: vec![],
            qself: None,
            path: to_syn_path(&pts.pat_ts_path),
            paren_token: syn::token::Paren {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            },
            elems: {
                let mut pats: Punctuated<syn::Pat, Comma> = Punctuated::new();
                pts.pat_ts_elems
                    .iter()
                    .for_each(|p| pats.push(to_syn_pat(p)));
                pats
            },
        }),
        Pat::PWild => syn::Pat::Wild(syn::PatWild {
            attrs: vec![],
            underscore_token: syn::token::Underscore {
                spans: [Span::call_site()],
            },
        }),
        Pat::PLit(lit) => syn::Pat::Lit({
            syn::PatLit {
                attrs: vec![],
                lit: to_syn_lit(lit),
            }
        }),
        Pat::PStruct(PatStruct {
            pat_struct_path,
            pat_struct_fields,
        }) => {
            let mut fields: Punctuated<syn::FieldPat, Comma> = Punctuated::new();
            pat_struct_fields.iter().for_each(|f| {
                fields.push(syn::FieldPat {
                    attrs: vec![],
                    member: syn::Member::Named(Ident::new(&f.field_pat_name, Span::call_site())),
                    colon_token: Some(Colon {
                        spans: [Span::call_site()],
                    }),
                    pat: Box::new(to_syn_pat(&f.field_pat_pat)),
                })
            });
            syn::Pat::Struct(syn::PatStruct {
                attrs: vec![],
                qself: None,
                path: to_syn_path_string(&vec![pat_struct_path.to_string()]),
                brace_token: Brace::default(),
                fields,
                rest: None,
            })
        }
        Pat::PTuple(pats) => {
            let mut spats: Punctuated<syn::Pat, Comma> = Punctuated::new();
            pats.iter().for_each(|p| spats.push(to_syn_pat(p)));
            syn::Pat::Tuple(syn::PatTuple {
                attrs: vec![],
                paren_token: Paren::default(),
                elems: spats,
            })
        }
        Pat::PTyp(p) => syn::Pat::Type(syn::PatType {
            attrs: vec![],
            pat: Box::new(to_syn_pat(&p.pat_typ_pat)),
            colon_token: Colon {
                spans: [Span::call_site()],
            },
            ty: Box::new(to_syn_typ(&p.pat_typ_typ)),
        }),
        Pat::PPath(p) => syn::Pat::Path(syn::PatPath {
            attrs: vec![],
            qself: None,
            path: to_syn_path(p),
        }),
    }
}

fn to_syn_stmt(s: &Stmt) -> syn::Stmt {
    match s {
        Stmt::SLocal(s) => match (&s.local_stmt_pat, &s.local_stmt_init) {
            (None, None) => panic!("SLocal with no pat and no init"),
            (None, Some(e)) => syn::Stmt::Expr(
                to_syn_expr(&e),
                Some(syn::token::Semi {
                    spans: [Span::call_site()],
                }),
            ),
            (Some(pat), _) => syn::Stmt::Local(Local {
                attrs: vec![],
                let_token: Let {
                    span: Span::call_site(),
                },
                pat: { to_syn_pat(&pat) },
                init: s.local_stmt_init.as_ref().map(|e| {
                    let e = to_syn_expr(&e);
                    LocalInit {
                        eq_token: Eq {
                            spans: [Span::call_site()],
                        },
                        expr: Box::new(e),
                        diverge: None,
                    }
                }),
                semi_token: Semi {
                    spans: [Span::call_site()],
                },
            }),
        },
        Stmt::SExpr(e) => {
            let e = to_syn_expr(&e);
            syn::Stmt::Expr(e, None)
        }
    }
}

fn to_syn_block(l: &Vec<Stmt>) -> Block {
    Block {
        brace_token: Brace::default(),
        stmts: l.iter().map(to_syn_stmt).collect(),
    }
}

fn to_syn_typ(t: &Typ) -> Type {
    match &t {
        Typ::TPath(v) => syn::Type::Path(syn::TypePath {
            qself: None,
            path: syn::Path {
                leading_colon: None,
                segments: v
                    .iter()
                    .map(|s| syn::PathSegment {
                        ident: Ident::new(&s.path_segment_name, Span::call_site()),
                        arguments: if s.path_segment_generic_args.len() == 0 {
                            syn::PathArguments::None
                        } else {
                            syn::PathArguments::AngleBracketed(
                                syn::AngleBracketedGenericArguments {
                                    colon2_token: None,
                                    lt_token: syn::token::Lt {
                                        spans: [Span::call_site()],
                                    },
                                    args: s
                                        .path_segment_generic_args
                                        .iter()
                                        .map(|t| syn::GenericArgument::Type(to_syn_typ(t)))
                                        .collect(),
                                    gt_token: syn::token::Gt {
                                        spans: [Span::call_site()],
                                    },
                                },
                            )
                        },
                    })
                    .collect(),
            },
        }),
        Typ::TReference(type_reference) => Type::Reference(syn::TypeReference {
            and_token: syn::token::And {
                spans: [Span::call_site()],
            },
            lifetime: None,
            mutability: if type_reference.type_reference_mut {
                Some(Mut {
                    span: Span::call_site(),
                })
            } else {
                None
            },
            elem: Box::new(to_syn_typ(&type_reference.type_reference_typ)),
        }),
        Typ::TSlice(t) => syn::Type::Slice(syn::TypeSlice {
            bracket_token: syn::token::Bracket {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            },
            elem: Box::new(to_syn_typ(&t)),
        }),
        Typ::TArray(TypeArray {
            type_array_elem,
            type_array_len,
        }) => syn::Type::Array(syn::TypeArray {
            bracket_token: syn::token::Bracket {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            },
            elem: Box::new(to_syn_typ(&type_array_elem)),
            semi_token: syn::token::Semi {
                spans: [Span::call_site()],
            },
            len: to_syn_expr(&type_array_len),
        }),
        Typ::TUnit => syn::Type::Tuple(syn::TypeTuple {
            paren_token: Paren::default(),
            elems: Punctuated::new(),
        }),
        Typ::TInfer => syn::Type::Infer(syn::TypeInfer {
            underscore_token: syn::token::Underscore {
                spans: [Span::call_site()],
            },
        }),
        Typ::TFn(TypeFn {
            type_fn_args,
            type_fn_ret,
        }) => syn::Type::BareFn(syn::TypeBareFn {
            lifetimes: None,
            unsafety: None,
            abi: None,
            fn_token: syn::token::Fn {
                span: Span::call_site(),
            },
            paren_token: Paren::default(),
            inputs: {
                let mut args: Punctuated<syn::BareFnArg, Comma> = Punctuated::new();
                type_fn_args.iter().for_each(|t| {
                    args.push(syn::BareFnArg {
                        attrs: vec![],
                        name: None,
                        ty: to_syn_typ(t),
                    })
                });
                args
            },
            variadic: None,
            output: ReturnType::Type(
                RArrow {
                    spans: [Span::call_site(), Span::call_site()],
                },
                Box::new(to_syn_typ(&type_fn_ret)),
            ),
        }),
        Typ::TTuple(ts) => syn::Type::Tuple(syn::TypeTuple {
            paren_token: Paren::default(),
            elems: {
                let mut types: Punctuated<syn::Type, Comma> = Punctuated::new();
                ts.iter().for_each(|t| types.push(to_syn_typ(t)));
                types
            },
        }),
    }
}

fn to_syn_fn_arg(a: &FnArg) -> syn::FnArg {
    let FnArg::FnArgPat(pt) = a;
    let t = to_syn_typ(&pt.pat_typ_typ);
    let pat: SynPat = to_syn_pat(&pt.pat_typ_pat);
    syn::FnArg::Typed(PatType {
        attrs: vec![],
        pat: Box::new(pat),
        colon_token: Colon {
            spans: [Span::call_site()],
        },
        ty: Box::new(t),
    })
}

fn generic_param_bounds(v: &Vec<Vec<String>>) -> Punctuated<syn::TypeParamBound, syn::token::Plus> {
    let mut bounds = Punctuated::new();
    v.iter().for_each(|p| {
        bounds.push(syn::TypeParamBound::Trait(syn::TraitBound {
            paren_token: None,
            modifier: syn::TraitBoundModifier::None,
            lifetimes: None,
            path: syn::Path {
                leading_colon: None,
                segments: {
                    let mut segs = Punctuated::new();
                    p.iter().for_each(|s| {
                        segs.push(syn::PathSegment {
                            ident: Ident::new(s, Span::call_site()),
                            arguments: syn::PathArguments::None,
                        })
                    });
                    segs
                },
            },
        }));
    });
    bounds
}

fn generic_params(generics: &Vec<GenericParam>) -> Punctuated<syn::GenericParam, Comma> {
    let mut syn_generics: Punctuated<syn::GenericParam, Comma> = Punctuated::new();
    generics.iter().for_each(|g| {
        let GenericParam::GenTypeParam(g) = g;
        let p = syn::GenericParam::Type(syn::TypeParam {
            attrs: vec![],
            ident: Ident::new(&g.generic_type_param_name, Span::call_site()),
            colon_token: None,
            bounds: generic_param_bounds(&g.generic_type_param_trait_bounds),
            eq_token: None,
            default: None,
        });
        syn_generics.push(p)
    });
    syn_generics
}

fn to_syn_fn_sig(s: &FnSig) -> Signature {
    let mut args: Punctuated<syn::FnArg, Comma> = Punctuated::new();
    s.fn_args.iter().for_each(|a| args.push(to_syn_fn_arg(a)));

    let generics: Punctuated<syn::GenericParam, Comma> = generic_params(&s.fn_generics);

    Signature {
        constness: if s.fn_const {
            Some(syn::token::Const {
                span: Span::call_site(),
            })
        } else {
            None
        },
        asyncness: None,
        unsafety: None,
        abi: None,
        fn_token: syn::token::Fn {
            span: Span::call_site(),
        },
        ident: Ident::new(&s.fn_name, Span::call_site()),
        generics: Generics {
            lt_token: None,
            params: generics,
            gt_token: None,
            where_clause: None,
        },
        paren_token: Paren::default(),
        inputs: args,
        variadic: None,
        output: ReturnType::Type(
            RArrow {
                spans: [Span::call_site(), Span::call_site()],
            },
            Box::new(to_syn_typ(&s.fn_ret_t)),
        ),
    }
}

fn to_syn_fn(f: &Fn) -> ItemFn {
    ItemFn {
        attrs: vec![],
        vis: Visibility::Public(Pub {
            span: Span::call_site(),
        }),
        sig: to_syn_fn_sig(&f.fn_sig),
        block: Box::new(to_syn_block(&f.fn_body)),
    }
}

fn to_syn_attr(attr: &Attribute) -> syn::Attribute {
    let Attribute::AttrDerive(s) = attr;
    syn::Attribute {
        pound_token: syn::token::Pound {
            spans: [Span::call_site()],
        },
        style: syn::AttrStyle::Outer,
        bracket_token: syn::token::Bracket {
            span: proc_macro2::Group::new(
                proc_macro2::Delimiter::None,
                proc_macro2::TokenStream::new(),
            )
            .delim_span(),
        },
        meta: syn::Meta::List(syn::MetaList {
            path: to_syn_path_string(&vec!["derive".to_string()]),
            delimiter: syn::MacroDelimiter::Paren(syn::token::Paren {
                span: proc_macro2::Group::new(
                    proc_macro2::Delimiter::None,
                    proc_macro2::TokenStream::new(),
                )
                .delim_span(),
            }),
            tokens: proc_macro2::TokenStream::from_str(s).unwrap(),
        }),
    }
}

#[allow(dead_code)]
fn use_enum_item(i: &Item) -> syn::Item {
    match i {
        Item::IEnum(ItemEnum { item_enum_name, .. }) => {
            let ut = syn::UseTree::Glob(syn::UseGlob {
                star_token: syn::token::Star {
                    spans: [Span::call_site()],
                },
            });
            let ut = syn::UseTree::Path(syn::UsePath {
                ident: Ident::new(&item_enum_name, Span::call_site()),
                colon2_token: syn::token::PathSep {
                    spans: [Span::call_site(), Span::call_site()],
                },
                tree: Box::new(ut),
            });
            let ut = syn::UseTree::Path(syn::UsePath {
                ident: Ident::new(&"crate", Span::call_site()),
                colon2_token: syn::token::PathSep {
                    spans: [Span::call_site(), Span::call_site()],
                },
                tree: Box::new(ut),
            });
            syn::Item::Use(syn::ItemUse {
                attrs: vec![],
                vis: Visibility::Inherited,
                use_token: syn::token::Use {
                    span: Span::call_site(),
                },
                leading_colon: None,
                tree: ut,
                semi_token: syn::token::Semi {
                    spans: [Span::call_site()],
                },
            })
        }
        _ => panic!("use_enum_item called with non-enum item"),
    }
}

fn to_syn_item(i: &Item) -> Vec<syn::Item> {
    match i {
        Item::IFn(f) => vec![syn::Item::Fn(to_syn_fn(f))],
        Item::IStruct(ItemStruct {
            item_struct_attrs,
            item_struct_name,
            item_struct_generics,
            item_struct_fields,
        }) => {
            let generics: Punctuated<syn::GenericParam, Comma> =
                generic_params(&item_struct_generics);
            let mut fields: Punctuated<syn::Field, Comma> = Punctuated::new();
            item_struct_fields.iter().for_each(|ft| {
                fields.push(syn::Field {
                    attrs: vec![],
                    vis: Visibility::Public(syn::token::Pub {
                        span: Span::call_site(),
                    }),
                    mutability: syn::FieldMutability::None,
                    ident: Some(Ident::new(&ft.field_typ_name, Span::call_site())),
                    colon_token: Some(Colon {
                        spans: [Span::call_site()],
                    }),
                    ty: to_syn_typ(&ft.field_typ_typ),
                })
            });
            let item = syn::Item::Struct(syn::ItemStruct {
                attrs: item_struct_attrs.iter().map(to_syn_attr).collect(),
                vis: syn::Visibility::Public({
                    syn::token::Pub {
                        span: Span::call_site(),
                    }
                }),
                struct_token: syn::token::Struct {
                    span: Span::call_site(),
                },
                ident: Ident::new(&item_struct_name, Span::call_site()),
                generics: syn::Generics {
                    lt_token: Some(syn::token::Lt {
                        spans: [Span::call_site()],
                    }),
                    params: generics,
                    gt_token: Some(syn::token::Gt {
                        spans: [Span::call_site()],
                    }),
                    where_clause: None,
                },
                fields: syn::Fields::Named(syn::FieldsNamed {
                    brace_token: syn::token::Brace {
                        span: proc_macro2::Group::new(
                            proc_macro2::Delimiter::None,
                            proc_macro2::TokenStream::new(),
                        )
                        .delim_span(),
                    },
                    named: fields,
                }),
                semi_token: Some(syn::token::Semi {
                    spans: [Span::call_site()],
                }),
            });
            vec![item]
        }
        Item::IType(ItemType {
            item_type_name,
            item_type_generics,
            item_type_typ,
        }) => {
            let generics: Punctuated<syn::GenericParam, Comma> =
                generic_params(&item_type_generics);
            let item = syn::Item::Type(syn::ItemType {
                attrs: vec![],
                vis: syn::Visibility::Public({
                    syn::token::Pub {
                        span: Span::call_site(),
                    }
                }),
                type_token: syn::token::Type {
                    span: Span::call_site(),
                },
                ident: Ident::new(&item_type_name, Span::call_site()),
                generics: syn::Generics {
                    lt_token: Some(syn::token::Lt {
                        spans: [Span::call_site()],
                    }),
                    params: generics,
                    gt_token: Some(syn::token::Gt {
                        spans: [Span::call_site()],
                    }),
                    where_clause: None,
                },
                eq_token: syn::token::Eq {
                    spans: [Span::call_site()],
                },
                ty: Box::new(to_syn_typ(&item_type_typ)),
                semi_token: syn::token::Semi {
                    spans: [Span::call_site()],
                },
            });
            vec![item]
        }
        Item::IEnum(ItemEnum {
            item_enum_attrs,
            item_enum_name,
            item_enum_generics,
            item_enum_variants,
        }) => {
            let generics: Punctuated<syn::GenericParam, Comma> =
                generic_params(&item_enum_generics);
            let mut variants: Punctuated<syn::Variant, Comma> = Punctuated::new();
            item_enum_variants.iter().for_each(|v| {
                let mut fields: Punctuated<syn::Field, Comma> = Punctuated::new();
                v.enum_variant_fields.iter().for_each(|t| {
                    fields.push(syn::Field {
                        attrs: vec![],
                        vis: Visibility::Inherited,
                        mutability: syn::FieldMutability::None,
                        ident: None,
                        colon_token: Some(Colon {
                            spans: [Span::call_site()],
                        }),
                        ty: to_syn_typ(&t),
                    })
                });
                variants.push(syn::Variant {
                    attrs: vec![],
                    ident: Ident::new(&v.enum_variant_name, Span::call_site()),
                    fields: if fields.len() > 0 {
                        syn::Fields::Unnamed(syn::FieldsUnnamed {
                            paren_token: syn::token::Paren {
                                span: proc_macro2::Group::new(
                                    proc_macro2::Delimiter::None,
                                    proc_macro2::TokenStream::new(),
                                )
                                .delim_span(),
                            },
                            unnamed: fields,
                        })
                    } else {
                        syn::Fields::Unit
                    },
                    discriminant: None,
                })
            });
            let item = syn::Item::Enum(syn::ItemEnum {
                attrs: item_enum_attrs.iter().map(to_syn_attr).collect(),
                vis: syn::Visibility::Public({
                    syn::token::Pub {
                        span: Span::call_site(),
                    }
                }),
                enum_token: syn::token::Enum {
                    span: Span::call_site(),
                },
                ident: Ident::new(&item_enum_name, Span::call_site()),
                generics: syn::Generics {
                    lt_token: Some(syn::token::Lt {
                        spans: [Span::call_site()],
                    }),
                    params: generics,
                    gt_token: Some(syn::token::Gt {
                        spans: [Span::call_site()],
                    }),
                    where_clause: None,
                },
                brace_token: Brace::default(),
                variants,
            });
            vec![item] //, use_enum_item(i)]
        }
        Item::IStatic(ItemStatic {
            item_static_name,
            item_static_typ,
            item_static_init,
        }) => {
            let item = syn::Item::Static(syn::ItemStatic {
                attrs: vec![],
                vis: syn::Visibility::Public({
                    syn::token::Pub {
                        span: Span::call_site(),
                    }
                }),
                static_token: syn::token::Static {
                    span: Span::call_site(),
                },
                mutability: syn::StaticMutability::None,
                // mutability: syn::StaticMutability::Mut(syn::token::Mut {
                //     span: Span::call_site(),
                // }),
                ident: Ident::new(&item_static_name, Span::call_site()),
                colon_token: Colon {
                    spans: [Span::call_site()],
                },
                ty: Box::new(to_syn_typ(&item_static_typ)),
                eq_token: syn::token::Eq {
                    spans: [Span::call_site()],
                },
                expr: Box::new(to_syn_expr(&item_static_init)),
                semi_token: syn::token::Semi {
                    spans: [Span::call_site()],
                },
            });
            vec![item]
        }
    }
}

fn to_syn_file(f: &File) -> syn::File {
    syn::File {
        shebang: None,
        attrs: vec![],
        items: f.file_items.iter().map(to_syn_item).flatten().collect(),
    }
}

fn file_to_syn_string(f: &File) -> String {
    let f: syn::File = to_syn_file(f);
    prettyplease::unparse(&f)
    // quote::quote!(#f).to_string()
}

// fn fn_to_syn_string(f: &Fn) -> String {
//     let f: ItemFn = to_syn_fn(f);
//     quote::quote!(#f).to_string()
// }

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match &self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Ne => "!=",
            BinOp::Eq => "==",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Rem => "%",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Mul => "*",
            BinOp::Shr => ">>",
            BinOp::Shl => "<<",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match &self {
            UnOp::Deref => "*",
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for ExprCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arg_s = self
            .call_args
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join(",");
        write!(f, "{}({})", self.call_fn.to_string(), arg_s)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Lit::LitInt(LitInt { lit_int_val, .. }) => write!(f, "{}", lit_int_val),
            Lit::LitBool(b) => write!(f, "{}", b),
            Lit::LitUnit => write!(f, "()"),
            Lit::LitString(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl fmt::Display for Pat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Pat::PIdent(p) => write!(
                f,
                "{}{}{}",
                if p.by_ref { "&" } else { "" },
                if p.is_mut { "mut " } else { "" },
                p.pat_name
            ),
            Pat::PTupleStruct(pts) => write!(
                f,
                "{}({})",
                pts.pat_ts_path
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
                pts.pat_ts_elems
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Pat::PWild => write!(f, "_"),
            Pat::PLit(lit) => write!(f, "{}", lit),
            Pat::PStruct(PatStruct {
                pat_struct_path,
                pat_struct_fields,
            }) => write!(
                f,
                "{} {{ {} }}",
                pat_struct_path,
                pat_struct_fields
                    .iter()
                    .map(|f| format!("{}:{}", f.field_pat_name, f.field_pat_pat))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Pat::PTuple(pats) => write!(
                f,
                "({})",
                pats.iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Pat::PTyp(p) => write!(f, "{}:{}", p.pat_typ_pat, p.pat_typ_typ),
            Pat::PPath(p) => write!(
                f,
                "{}",
                p.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("::")
            ),
        }
    }
}

impl fmt::Display for Arm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} => {}", self.arm_pat, self.arm_body)
    }
}

impl fmt::Display for PathSegment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path_segment_name)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Expr::EBinOp(e) => write!(f, "{} {} {}", e.expr_bin_left, e.op, e.expr_bin_right),
            Expr::EPath(s) => write!(
                f,
                "{}",
                s.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("::")
            ),
            Expr::ECall(e) => write!(f, "{}", e),
            Expr::EUnOp(e) => write!(f, "{} {}", e.expr_unary_op, e.expr_unary_expr),
            Expr::EAssign(e) => write!(f, "{} = {}", e.expr_assign_l, e.expr_assign_r),
            Expr::EBlock(stmts) => write!(
                f,
                "{{ {} }}",
                stmts
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(";\n")
            ),
            Expr::ELit(lit) => write!(f, "{}", lit),
            Expr::EIf(ExprIf {
                expr_if_cond,
                expr_if_then,
                expr_if_else,
            }) => {
                let if_then = expr_if_then
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(";\n");
                let if_else = match expr_if_else {
                    None => "".to_string(),
                    Some(e) => format!("else {}", e),
                };
                write!(f, "if {} {{ {} }} {}", expr_if_cond, if_then, if_else)
            }
            Expr::EWhile(ExprWhile {
                expr_while_cond,
                expr_while_body,
            }) => {
                let while_body = expr_while_body
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(";\n");
                write!(f, "while {} {{ {} }}", expr_while_cond, while_body)
            }
            Expr::EIndex(ExprIndex {
                expr_index_base,
                expr_index_index,
            }) => write!(f, "{}[{}]", expr_index_base, expr_index_index),
            Expr::ERepeat(ExprRepeat {
                expr_repeat_elem,
                expr_repeat_len,
            }) => write!(f, "[{}; {}]", expr_repeat_elem, expr_repeat_len),
            Expr::EReference(ExprReference {
                expr_reference_is_mut,
                expr_reference_expr,
            }) => write!(
                f,
                "&{} {}",
                if *expr_reference_is_mut { "mut" } else { "" },
                expr_reference_expr
            ),
            Expr::EMatch(ExprMatch {
                expr_match_expr,
                expr_match_arms,
            }) => write!(
                f,
                "match {} {{ {} }}",
                expr_match_expr,
                expr_match_arms
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join("|")
            ),
            Expr::EField(ExprField {
                expr_field_base,
                expr_field_name,
                ..
            }) => write!(f, "{}.{}", expr_field_base, expr_field_name),
            Expr::EStruct(ExprStruct {
                expr_struct_path,
                expr_struct_fields,
            }) => write!(
                f,
                "{} {{ {} }}",
                expr_struct_path
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
                expr_struct_fields
                    .iter()
                    .map(|f| format!("{}:{}", f.field_val_name, f.field_val_expr))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Expr::ETuple(es) => write!(
                f,
                "({})",
                es.iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Expr::EMethodCall(ExprMethodCall {
                expr_method_call_receiver,
                expr_method_call_name,
                expr_method_call_args,
            }) => write!(
                f,
                "{}.{}({})",
                expr_method_call_receiver,
                expr_method_call_name,
                expr_method_call_args
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Expr::ECast(ExprCast {
                expr_cast_expr,
                expr_cast_type,
            }) => write!(
                f,
                "{} as {}",
                expr_cast_expr,
                expr_cast_type,
            ),
        }
    }
}

impl fmt::Display for Typ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Typ::TPath(v) => write!(
                f,
                "{}",
                v.iter()
                    .map(|s| if s.path_segment_generic_args.len() == 0 {
                        s.path_segment_name.to_string()
                    } else {
                        format!(
                            "{}<{}>",
                            s.path_segment_name,
                            s.path_segment_generic_args
                                .iter()
                                .map(|t| t.to_string())
                                .collect::<Vec<_>>()
                                .join(",")
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("::")
            ),
            Typ::TReference(type_reference) => write!(
                f,
                "&{} {}",
                if type_reference.type_reference_mut {
                    "mut"
                } else {
                    ""
                },
                type_reference.type_reference_typ
            ),
            Typ::TSlice(t) => write!(f, "[{}]", t),
            Typ::TArray(TypeArray {
                type_array_elem,
                type_array_len,
            }) => write!(f, "[{}; {}]", type_array_elem, type_array_len),
            Typ::TUnit => write!(f, "()"),
            Typ::TInfer => write!(f, "_"),
            Typ::TFn(TypeFn {
                type_fn_args,
                type_fn_ret,
            }) => write!(
                f,
                "({}) -> {}",
                type_fn_args
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                type_fn_ret
            ),
            Typ::TTuple(ts) => write!(
                f,
                "({})",
                ts.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }
}

impl fmt::Display for LocalStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "let {} {}",
            self.local_stmt_pat
                .as_ref()
                .map_or("".to_string(), |p| p.to_string()),
            if let Some(e) = &self.local_stmt_init {
                format!("= {}", e)
            } else {
                "".to_string()
            }
        )
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Stmt::SLocal(s) => write!(f, "{}", s),
            Stmt::SExpr(e) => write!(f, "{}", e),
        }
    }
}

impl fmt::Display for FnArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let FnArg::FnArgPat(pt) = &self;
        write!(f, "{}:{}", pt.pat_typ_pat, pt.pat_typ_typ)
    }
}

impl fmt::Display for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fn {}({}) -> {}",
            self.fn_name,
            self.fn_args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
            self.fn_ret_t
        )
    }
}

impl fmt::Display for Fn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {{ {} }}",
            self.fn_sig,
            self.fn_body
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(";")
        )
    }
}

impl fmt::Display for FieldTyp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.field_typ_name, self.field_typ_typ)
    }
}

impl fmt::Display for EnumVariant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.enum_variant_name,
            self.enum_variant_fields
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Item::IFn(func) => write!(f, "{}", func),
            Item::IStruct(ItemStruct {
                item_struct_name,
                item_struct_fields,
                ..
            }) => write!(
                f,
                "struct {} {{ {} }}",
                item_struct_name,
                item_struct_fields
                    .iter()
                    .map(|ft| ft.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Item::IType(ItemType {
                item_type_name,
                item_type_typ,
                ..
            }) => write!(f, "type {} = {}", item_type_name, item_type_typ),
            Item::IEnum(ItemEnum {
                item_enum_name,
                item_enum_variants,
                ..
            }) => write!(
                f,
                "enum {} {{ {} }}",
                item_enum_name,
                item_enum_variants
                    .iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Item::IStatic(ItemStatic {
                item_static_name,
                item_static_typ,
                item_static_init,
            }) => write!(
                f,
                "static {}: {} = {}",
                item_static_name, item_static_typ, item_static_init
            ),
        }
    }
}

impl fmt::Display for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.file_items
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

ocaml_export! {
  fn rust_fn_to_string(cr, e:OCamlRef<Fn>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Fn = e.to_rust ();
    fn_to_string(&e).to_owned ().to_ocaml(cr)
  }

  fn rust_expr_to_string(cr, e:OCamlRef<Expr>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Expr = e.to_rust ();
    e.to_string().to_owned().to_ocaml(cr)
  }

  fn rust_typ_to_string(cr, e:OCamlRef<Typ>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Typ = e.to_rust ();
    e.to_string().to_owned().to_ocaml(cr)
  }

  fn rust_file_to_syn_string(cr, e:OCamlRef<File>) -> OCaml<String> {
    let e = cr.get(e);
    let e: File = e.to_rust ();
    file_to_syn_string(&e).to_owned ().to_ocaml(cr)
  }

  // fn rust_add_2(cr, x:OCamlRef<OCamlInt64>) -> OCaml<String> {
  //   let x: OCaml<OCamlInt64> = cr.get(x);
  //   let x: i64 = FromOCaml::from_ocaml(x);
  //   let z = x + 2;
  //   z.to_string().to_owned().to_ocaml(cr)
  // }

  // fn rust_dflt(cr, x:OCamlRef<Option<OCamlInt64>>) -> OCaml<String> {
  //   let x: OCaml<Option<OCamlInt64>> = cr.get(x);
  //   let x: Option<i64> = FromOCaml::from_ocaml(x);
  //   let z = match x {
  //     Some(x) => x,
  //     None => 0,
  //   };
  //   z.to_string().to_owned().to_ocaml(cr)
  // }
}

// use std::sync::Mutex;

// fn test(m: Mutex<i32>) -> Mutex<i32 {
//     let mut data = m.lock().unwrap();
//     *data = 5;
//     let x = std::mem::replace::<i32>(&mut data, 6);
//     let y = *data;
//     drop(data);
// }
