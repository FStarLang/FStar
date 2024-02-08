use ocaml_interop::{
    impl_from_ocaml_record, impl_from_ocaml_variant, ocaml_export, OCaml, OCamlList, OCamlRef,
    ToOCaml,
};
use proc_macro2::Span;
use syn::{
    punctuated::Punctuated, token::Brace, token::Colon, token::Comma, token::Eq, token::Let,
    token::Mut, token::Paren, token::Pub, token::RArrow, token::Ref, token::Semi, Block, Generics,
    Ident, ItemFn, Local, LocalInit, Pat as SynPat, PatType, Path, PathArguments, PathSegment,
    ReturnType, Signature, Type, Visibility,
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

enum Expr {
    EBinOp(ExprBin),
    EPath(Vec<String>),
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
}

struct TypeReference {
    type_reference_mut: bool,
    type_reference_typ: Box<Typ>,
}

struct TypePathSegment {
    type_path_segment_name: String,
    type_path_segment_generic_args: Vec<Typ>,
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
    TPath(Vec<TypePathSegment>),
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
    pat_ts_path: String,
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
      BinOp::Mul
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
    Expr::EPath (payload:OCamlList<String>),
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
  TypeReference {
    type_reference_mut: bool,
    type_reference_typ: Typ,
  }
}

impl_from_ocaml_record! {
  TypePathSegment {
    type_path_segment_name: String,
    type_path_segment_generic_args: OCamlList<Typ>,
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
    Typ::TPath (payload:OCamlList<TypePathSegment>),
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
    pat_ts_path : String,
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

fn to_syn_path(s: &Vec<String>) -> syn::Path {
    let mut segs: Punctuated<syn::PathSegment, syn::token::PathSep> = Punctuated::new();
    s.iter().for_each(|s| {
        segs.push(PathSegment {
            ident: Ident::new(&s, Span::call_site()),
            arguments: PathArguments::None,
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
    }
}

fn is_vec_new(e: &Expr) -> bool {
    match e {
        Expr::EPath(s) => s[0] == VEC_NEW_FN,
        _ => false,
    }
}

fn is_panic(e: &Expr) -> bool {
    match e {
        Expr::EPath(s) => s[0] == PANIC_FN,
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
            path: to_syn_path(&vec!["vec".to_string()]),
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
            path: to_syn_path(&vec!["panic".to_string()]),
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
                path: to_syn_path(expr_struct_path),
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
        }
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
            path: to_syn_path(&vec![pts.pat_ts_path.to_string()]),
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
                path: to_syn_path(&vec![pat_struct_path.to_string()]),
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
                        ident: Ident::new(&s.type_path_segment_name, Span::call_site()),
                        arguments: if s.type_path_segment_generic_args.len() == 0 {
                            syn::PathArguments::None
                        } else {
                            syn::PathArguments::AngleBracketed(
                                syn::AngleBracketedGenericArguments {
                                    colon2_token: None,
                                    lt_token: syn::token::Lt {
                                        spans: [Span::call_site()],
                                    },
                                    args: s
                                        .type_path_segment_generic_args
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
            path: to_syn_path(&vec!["derive".to_string()]),
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
                    vis: Visibility::Inherited,
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
            vec![item, use_enum_item(i)]
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
    quote::quote!(#f).to_string()
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
                pts.pat_ts_path,
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
        }
    }
}

impl fmt::Display for Arm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} => {}", self.arm_pat, self.arm_body)
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
                    .map(|s| if s.type_path_segment_generic_args.len() == 0 {
                        s.type_path_segment_name.to_string()
                    } else {
                        format!(
                            "{}<{}>",
                            s.type_path_segment_name,
                            s.type_path_segment_generic_args
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
// struct S {
//     v: Vec<i32>,
//     f: u32,
// }

// const fn new_mutex() -> Mutex<S> {
//     Mutex::new(S { v: vec![], f: 0 })
// }

// static OBJ: Mutex<S> = new_mutex();

type hashable_len = usize;
type signable_len = usize;
type hkdf_lbl_len = usize;
type hkdf_ikm_len = usize;
type alg_t = ();

pub const dice_digest_len: usize = 32;

pub const dice_hash_alg: () = ();

pub fn ed25519_verify(
    pubk: &mut [u8],
    hdr: &mut [u8],
    hdr_len: signable_len,
    sig: &mut [u8],
    ppubk: (),
    phdr: (),
    psig: (),
    pubk_seq: (),
    hdr_seq: (),
    sig_seq: (),
) -> bool {
    panic!()
}

pub fn hacl_hash(
    alg: (),
    src_len: hashable_len,
    src: &mut [u8],
    dst: &mut [u8],
    psrc: (),
    src_seq: (),
    dst_seq: (),
) -> () {
    panic!()
}

pub fn compare(
    len: usize,
    a: &mut [u8],
    b: &mut [u8],
    p: (),
    a_seq: (),
    b_seq: (),
    __c0: (),
) -> bool {
    panic!()
}

pub fn memcpy<A>(l: usize, src: &mut [A], dst: &mut [A], p: (), src0: (), dst0: ()) -> () {
    panic!()
}

pub fn zeroize(len: usize, src: &mut [u8], s: ()) -> () {
    panic!()
}

pub fn hacl_hmac(
    alg: (),
    dst: &mut [u8],
    key: &mut [u8],
    key_len: hashable_len,
    msg: &mut [u8],
    msg_len: hashable_len,
    pkey: (),
    pmsg: (),
    dst_seq: (),
    key_seq: (),
    msg_seq: (),
) -> () {
    panic!()
}

pub fn x509_get_deviceIDCRI(
    version: x509_version_t,
    s_common: String,
    s_org: String,
    s_country: String,
    ku: u32,
    deviceID_pub: &mut [u8],
    pub_perm: (),
    deviceID_pub0: (),
) -> deviceIDCRI_t {
    panic!()
}

pub fn serialize_deviceIDCRI(
    deviceIDCRI: deviceIDCRI_t,
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCRI_buf0: (),
) -> () {
    panic!()
}

pub fn x509_get_deviceIDCSR(
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCRI_sig: &mut [u8],
    buf_perm: (),
    sig_perm: (),
    buf: (),
    sig: (),
) -> deviceIDCSR_t {
    panic!()
}

pub fn ed25519_sign(
    buf: &mut [u8],
    privk: &mut [u8],
    len: usize,
    msg: &mut [u8],
    pprivk: (),
    pmsg: (),
    buf0: (),
    privk_seq: (),
    msg_seq: (),
) -> () {
    panic!()
}

pub fn serialize_deviceIDCSR(
    deviceIDCRI_len: usize,
    deviceIDCSR: deviceIDCSR_t,
    deviceIDCSR_len: usize,
    deviceIDCSR_buf: &mut [u8],
    _buf: (),
) -> () {
    panic!()
}

pub fn x509_get_aliasKeyTBS(
    aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
    fwid: &mut [u8],
    deviceID_pub: &mut [u8],
    aliasKey_pub: &mut [u8],
    fwid_perm: (),
    deviceID_perm: (),
    aliasKey_perm: (),
    fwid0: (),
    deviceID0: (),
    aliasKey0: (),
) -> aliasKeyTBS_t {
    panic!()
}

pub fn serialize_aliasKeyTBS(
    aliasKeyTBS: aliasKeyTBS_t,
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyTBS_buf0: (),
) -> () {
    panic!()
}

pub fn x509_get_aliasKeyCRT(
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyTBS_sig: &mut [u8],
    buf_perm: (),
    sig_perm: (),
    buf: (),
    sig: (),
) -> aliasKeyCRT_t {
    panic!()
}

pub fn serialize_aliasKeyCRT(
    aliasKeyTBS_len: usize,
    aliasKeyCRT: aliasKeyCRT_t,
    aliasKeyCRT_len: usize,
    aliasKeyCRT_buf: &mut [u8],
    _buf: (),
) -> () {
    panic!()
}

pub fn digest_len(alg: alg_t) -> usize {
    panic!()
}

pub const v32us: usize = 32;

//////////////////////////////

pub static uds_len: hashable_len = 1;
pub enum dice_return_code {
    DICE_SUCCESS,
    DICE_ERROR,
}
use crate::dice_return_code::*;
pub struct engine_record_t {
    l0_image_header_size: signable_len,
    l0_image_header: std::vec::Vec<u8>,
    l0_image_header_sig: std::vec::Vec<u8>,
    l0_binary_size: hashable_len,
    l0_binary: std::vec::Vec<u8>,
    l0_binary_hash: std::vec::Vec<u8>,
    l0_image_auth_pubkey: std::vec::Vec<u8>,
}
pub fn authenticate_l0_image(
    mut record: engine_record_t,
    repr: (),
    p: (),
) -> (engine_record_t, bool) {
    let valid_header_sig = ed25519_verify(
        &mut record.l0_image_auth_pubkey,
        &mut record.l0_image_header,
        record.l0_image_header_size,
        &mut record.l0_image_header_sig,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    let mut b = false;
    let b1 = if valid_header_sig {
        let hash_buf = &mut [0; dice_digest_len];
        hacl_hash(
            dice_hash_alg,
            record.l0_binary_size,
            &mut record.l0_binary,
            hash_buf,
            (),
            (),
            (),
        );
        let res = compare(
            dice_digest_len,
            hash_buf,
            &mut record.l0_binary_hash,
            (),
            (),
            (),
            (),
        );
        let res1 = (record, res);
        let hash_buf1 = res1;
        hash_buf1
    } else {
        let res = (record, false);
        res
    };
    b1
}
pub fn compute_cdi(
    cdi: &mut [u8],
    uds: &mut [u8],
    mut record: engine_record_t,
    uds_perm: (),
    p: (),
    uds_bytes: (),
    __c0: (),
    __repr: (),
) -> engine_record_t {
    let uds_digest = &mut [0; dice_digest_len];
    let l0_digest = &mut [0; dice_digest_len];
    hacl_hash(dice_hash_alg, uds_len, uds, uds_digest, (), (), ());
    hacl_hash(
        dice_hash_alg,
        record.l0_binary_size,
        &mut record.l0_binary,
        l0_digest,
        (),
        (),
        (),
    );
    hacl_hmac(
        dice_hash_alg,
        cdi,
        uds_digest,
        dice_digest_len,
        l0_digest,
        dice_digest_len,
        (),
        (),
        (),
        (),
        (),
    );
    let l0_digest1 = record;
    let uds_digest1 = l0_digest1;
    uds_digest1
}
pub fn engine_main_aux(
    cdi: &mut [u8],
    uds: &mut [u8],
    mut record: engine_record_t,
    c0: (),
    repr: (),
    uds_perm: (),
    p: (),
    uds_bytes: (),
) -> (engine_record_t, dice_return_code) {
    let b = authenticate_l0_image(record, (), ());
    if b.1 {
        let record1 = compute_cdi(cdi, uds, b.0, (), (), (), (), ());
        let res = (record1, dice_return_code::DICE_SUCCESS);
        res
    } else {
        let res = (b.0, dice_return_code::DICE_ERROR);
        res
    }
}
pub static engine_main: fn(
    &mut [u8],
    &mut [u8],
    engine_record_t,
    (),
    (),
    (),
    (),
    (),
) -> (engine_record_t, dice_return_code) = engine_main_aux;
pub type x509_version_t = u32;
pub type x509_serialNumber_t = u32;
pub type deviceIDCRI_t = u32;
pub type deviceIDCSR_t = u32;
pub type aliasKeyTBS_t = u32;
pub type aliasKeyCRT_t = u32;
pub struct deviceIDCSR_ingredients_t {
    ku: u32,
    version: x509_version_t,
    s_common: String,
    s_org: String,
    s_country: String,
}
pub struct aliasKeyCRT_ingredients_t {
    version1: x509_version_t,
    serialNumber: x509_serialNumber_t,
    i_common: String,
    i_org: String,
    i_country: String,
    notBefore: usize,
    notAfter: usize,
    s_common1: String,
    s_org1: String,
    s_country1: String,
    ku1: u32,
    l0_version: u32,
}
pub struct l0_record_t {
    fwid: std::vec::Vec<u8>,
    deviceID_label_len: hkdf_lbl_len,
    deviceID_label: std::vec::Vec<u8>,
    aliasKey_label_len: hkdf_lbl_len,
    aliasKey_label: std::vec::Vec<u8>,
    deviceIDCSR_ingredients: deviceIDCSR_ingredients_t,
    aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
}
pub fn derive_key_pair_aux(
    pubk: &mut [u8],
    privk: &mut [u8],
    ikm_len: hkdf_ikm_len,
    ikm: &mut [u8],
    lbl_len: hkdf_lbl_len,
    lbl: &mut [u8],
    ikm_perm: (),
    lbl_perm: (),
    _pub_seq: (),
    _priv_seq: (),
    ikm_seq: (),
    lbl_seq: (),
) -> () {
    panic!()
}
pub static derive_key_pair: fn(
    &mut [u8],
    &mut [u8],
    hkdf_ikm_len,
    &mut [u8],
    hkdf_lbl_len,
    &mut [u8],
    (),
    (),
    (),
    (),
    (),
    (),
) -> () = derive_key_pair_aux;
pub fn derive_DeviceID_aux(
    alg: alg_t,
    deviceID_pub: &mut [u8],
    deviceID_priv: &mut [u8],
    cdi: &mut [u8],
    deviceID_label_len: hkdf_lbl_len,
    deviceID_label: &mut [u8],
    cdi0: (),
    deviceID_label0: (),
    deviceID_pub0: (),
    deviceID_priv0: (),
    cdi_perm: (),
    p: (),
) -> () {
    let mut cdigest = vec![0; digest_len(alg)];
    hacl_hash(alg, dice_digest_len, cdi, &mut cdigest, (), (), ());
    derive_key_pair(
        deviceID_pub,
        deviceID_priv,
        digest_len(alg),
        &mut cdigest,
        deviceID_label_len,
        deviceID_label,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    drop(cdigest)
}
pub static derive_DeviceID: fn(
    alg_t,
    &mut [u8],
    &mut [u8],
    &mut [u8],
    hkdf_lbl_len,
    &mut [u8],
    (),
    (),
    (),
    (),
    (),
    (),
) -> () = derive_DeviceID_aux;
pub fn derive_AliasKey_aux(
    alg: alg_t,
    aliasKey_pub: &mut [u8],
    aliasKey_priv: &mut [u8],
    cdi: &mut [u8],
    fwid: &mut [u8],
    aliasKey_label_len: hkdf_lbl_len,
    aliasKey_label: &mut [u8],
    cdi0: (),
    fwid0: (),
    aliasKey_label0: (),
    aliasKey_pub0: (),
    aliasKey_priv0: (),
    cdi_perm: (),
    p: (),
) -> () {
    let mut cdigest = vec![0; digest_len(alg)];
    let mut adigest = vec![0; digest_len(alg)];
    hacl_hash(alg, dice_digest_len, cdi, &mut cdigest, (), (), ());
    hacl_hmac(
        alg,
        &mut adigest,
        &mut cdigest,
        digest_len(alg),
        fwid,
        v32us,
        (),
        (),
        (),
        (),
        (),
    );
    derive_key_pair(
        aliasKey_pub,
        aliasKey_priv,
        digest_len(alg),
        &mut adigest,
        aliasKey_label_len,
        aliasKey_label,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    drop(cdigest);
    drop(adigest)
}
pub static derive_AliasKey: fn(
    alg_t,
    &mut [u8],
    &mut [u8],
    &mut [u8],
    &mut [u8],
    hkdf_lbl_len,
    &mut [u8],
    (),
    (),
    (),
    (),
    (),
    (),
    (),
) -> () = derive_AliasKey_aux;
pub fn derive_AuthKeyID_aux(
    alg: alg_t,
    authKeyID: &mut [u8],
    deviceID_pub: &mut [u8],
    authKeyID0: (),
    deviceID_pub0: (),
    p: (),
) -> () {
    hacl_hash(alg, v32us, deviceID_pub, authKeyID, (), (), ())
}
pub static derive_AuthKeyID: fn(alg_t, &mut [u8], &mut [u8], (), (), ()) -> () =
    derive_AuthKeyID_aux;
pub fn create_deviceIDCRI(
    pub_perm: (),
    pub_seq: (),
    _buf: (),
    deviceID_pub: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCSR_ingredients: deviceIDCSR_ingredients_t,
) -> () {
    let deviceIDCRI = x509_get_deviceIDCRI(
        deviceIDCSR_ingredients.version,
        deviceIDCSR_ingredients.s_common,
        deviceIDCSR_ingredients.s_org,
        deviceIDCSR_ingredients.s_country,
        deviceIDCSR_ingredients.ku,
        deviceID_pub,
        (),
        (),
    );
    serialize_deviceIDCRI(deviceIDCRI, deviceIDCRI_len, deviceIDCRI_buf, ())
}
pub fn sign_and_finalize_deviceIDCSR(
    priv_perm: (),
    priv_seq: (),
    _cri_buf: (),
    _csr_buf: (),
    deviceID_priv: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCSR_len: usize,
    deviceIDCSR_buf: &mut [u8],
    deviceIDCSR_ingredients: (),
) -> () {
    let mut deviceIDCRI_sig = vec![0; deviceIDCRI_len];
    ed25519_sign(
        &mut deviceIDCRI_sig,
        deviceID_priv,
        deviceIDCRI_len,
        deviceIDCRI_buf,
        (),
        (),
        (),
        (),
        (),
    );
    let deviceIDCSR = x509_get_deviceIDCSR(
        deviceIDCRI_len,
        deviceIDCRI_buf,
        &mut deviceIDCRI_sig,
        (),
        (),
        (),
        (),
    );
    drop(deviceIDCRI_sig);
    serialize_deviceIDCSR(
        deviceIDCRI_len,
        deviceIDCSR,
        deviceIDCSR_len,
        deviceIDCSR_buf,
        (),
    )
}
pub fn create_aliasKeyTBS(
    fwid_perm: (),
    authKey_perm: (),
    device_perm: (),
    aliasKey_perm: (),
    fwid0: (),
    authKeyID0: (),
    deviceID_pub0: (),
    aliasKey_pub0: (),
    _buf: (),
    fwid: &mut [u8],
    authKeyID: &mut [u8],
    deviceID_pub: &mut [u8],
    aliasKey_pub: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
) -> () {
    let aliasKeyTBS = x509_get_aliasKeyTBS(
        aliasKeyCRT_ingredients,
        fwid,
        deviceID_pub,
        aliasKey_pub,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    serialize_aliasKeyTBS(aliasKeyTBS, aliasKeyTBS_len, aliasKeyTBS_buf, ())
}
pub fn sign_and_finalize_aliasKeyCRT(
    priv_perm: (),
    priv_seq: (),
    _tbs_buf: (),
    _crt_buf: (),
    deviceID_priv: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyCRT_len: usize,
    aliasKeyCRT_buf: &mut [u8],
    aliasKeyCRT_ingredients: (),
) -> () {
    let mut aliasKeyTBS_sig = vec![0; aliasKeyTBS_len];
    ed25519_sign(
        &mut aliasKeyTBS_sig,
        deviceID_priv,
        aliasKeyTBS_len,
        aliasKeyTBS_buf,
        (),
        (),
        (),
        (),
        (),
    );
    let aliasKeyCRT = x509_get_aliasKeyCRT(
        aliasKeyTBS_len,
        aliasKeyTBS_buf,
        &mut aliasKeyTBS_sig,
        (),
        (),
        (),
        (),
    );
    drop(aliasKeyTBS_sig);
    serialize_aliasKeyCRT(
        aliasKeyTBS_len,
        aliasKeyCRT,
        aliasKeyCRT_len,
        aliasKeyCRT_buf,
        (),
    )
}
pub fn l0_main_aux(
    cdi: &mut [u8],
    deviceID_pub: &mut [u8],
    deviceID_priv: &mut [u8],
    aliasKey_pub: &mut [u8],
    aliasKey_priv: &mut [u8],
    aliasKeyTBS_len: usize,
    aliasKeyCRT_len: usize,
    aliasKeyCRT: &mut [u8],
    deviceIDCRI_len: usize,
    deviceIDCSR_len: usize,
    deviceIDCSR: &mut [u8],
    mut record: l0_record_t,
    repr: (),
    cdi0: (),
    deviceID_pub0: (),
    deviceID_priv0: (),
    aliasKey_pub0: (),
    aliasKey_priv0: (),
    aliasKeyCRT0: (),
    deviceIDCSR0: (),
    cdi_perm: (),
    p: (),
) -> () {
    derive_DeviceID(
        dice_hash_alg,
        deviceID_pub,
        deviceID_priv,
        cdi,
        record.deviceID_label_len,
        &mut record.deviceID_label,
        (),
        (),
        (),
        (),
        (),
        (),
    );
    derive_AliasKey(
        dice_hash_alg,
        aliasKey_pub,
        aliasKey_priv,
        cdi,
        &mut record.fwid,
        record.aliasKey_label_len,
        &mut record.aliasKey_label,
        (),
        (),
        (),
        (),
        (),
        (),
        (),
    );
    let mut authKeyID = vec![0; dice_digest_len];
    derive_AuthKeyID(dice_hash_alg, &mut authKeyID, deviceID_pub, (), (), ());
    let mut deviceIDCRI = vec![0; deviceIDCRI_len];
    create_deviceIDCRI(
        (),
        (),
        (),
        deviceID_pub,
        deviceIDCRI_len,
        &mut deviceIDCRI,
        record.deviceIDCSR_ingredients,
    );
    sign_and_finalize_deviceIDCSR(
        (),
        (),
        (),
        (),
        deviceID_priv,
        deviceIDCRI_len,
        &mut deviceIDCRI,
        deviceIDCSR_len,
        deviceIDCSR,
        (),
    );
    let mut aliasKeyTBS = vec![0; aliasKeyTBS_len];
    create_aliasKeyTBS(
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        (),
        &mut record.fwid,
        &mut authKeyID,
        deviceID_pub,
        aliasKey_pub,
        aliasKeyTBS_len,
        &mut aliasKeyTBS,
        record.aliasKeyCRT_ingredients,
    );
    sign_and_finalize_aliasKeyCRT(
        (),
        (),
        (),
        (),
        deviceID_priv,
        aliasKeyTBS_len,
        &mut aliasKeyTBS,
        aliasKeyCRT_len,
        aliasKeyCRT,
        (),
    );
    drop(authKeyID);
    drop(deviceIDCRI);
    drop(aliasKeyTBS);
}
pub static l0_main: fn(
    &mut [u8],
    &mut [u8],
    &mut [u8],
    &mut [u8],
    &mut [u8],
    usize,
    usize,
    &mut [u8],
    usize,
    usize,
    &mut [u8],
    l0_record_t,
    (),
    (),
    (),
    (),
    (),
    (),
    (),
    (),
    (),
    (),
) -> () = l0_main_aux;
pub struct profile_descriptor_t {
    name: String,
    dpe_spec_version: u32,
    max_message_size: u32,
    uses_multi_part_messages: bool,
    supports_concurrent_operations: bool,
    supports_encrypted_sessions: bool,
    supports_derived_sessions: bool,
    max_sessions: usize,
    session_protocol: String,
    supports_session_sync: bool,
    session_sync_policy: String,
    session_migration_protocol: String,
    supports_default_context: bool,
    supports_context_handles: bool,
    max_contexts_per_session: usize,
    max_context_handle_size: usize,
    supports_auto_init: bool,
    supports_simulation: bool,
    supports_attestation: bool,
    supports_sealing: bool,
    supports_get_profile: bool,
    supports_open_session: bool,
    supports_close_session: bool,
    supports_sync_session: bool,
    supports_export_session: bool,
    supports_import_session: bool,
    supports_init_context: bool,
    supports_certify_key: bool,
    supports_sign: bool,
    supports_seal: bool,
    supports_unseal: bool,
    supports_sealing_public: bool,
    supports_rotate_context_handle: bool,
    dice_derivation: String,
    asymmetric_derivation: String,
    symmetric_derivation: String,
    supports_any_label: bool,
    supported_labels: String,
    initial_derivation: String,
    input_format: String,
    supports_internal_inputs: bool,
    supports_internal_dpe_info: bool,
    supports_internal_dpe_dice: bool,
    internal_dpe_info_type: String,
    internal_dpe_dice_type: String,
    internal_inputs: String,
    supports_certificates: bool,
    max_certificate_size: usize,
    max_certificate_chain_size: usize,
    appends_more_certificates: bool,
    supports_certificate_policies: bool,
    supports_policy_identity_init: bool,
    supports_policy_identity_loc: bool,
    supports_policy_attest_init: bool,
    supports_policy_attest_loc: bool,
    supports_policy_assert_init: bool,
    supports_policy_assert_loc: bool,
    certificate_policies: String,
    supports_eca_certificates: bool,
    eca_certificate_format: String,
    leaf_certificate_format: String,
    public_key_format: String,
    supports_external_key: bool,
    to_be_signed_format: String,
    signature_format: String,
    supports_symmetric_sign: bool,
    supports_asymmetric_unseal: bool,
    supports_unseal_policy: bool,
    unseal_policy_format: String,
}
pub fn mk_profile_descriptor(
    name: String,
    dpe_spec_version: u32,
    max_message_size: u32,
    uses_multi_part_messages: bool,
    supports_concurrent_operations: bool,
    supports_encrypted_sessions: bool,
    supports_derived_sessions: bool,
    max_sessions: usize,
    session_protocol: String,
    supports_session_sync: bool,
    session_sync_policy: String,
    session_migration_protocol: String,
    supports_default_context: bool,
    supports_context_handles: bool,
    max_contexts_per_session: usize,
    max_context_handle_size: usize,
    supports_auto_init: bool,
    supports_simulation: bool,
    supports_attestation: bool,
    supports_sealing: bool,
    supports_get_profile: bool,
    supports_open_session: bool,
    supports_close_session: bool,
    supports_sync_session: bool,
    supports_export_session: bool,
    supports_import_session: bool,
    supports_init_context: bool,
    supports_certify_key: bool,
    supports_sign: bool,
    supports_seal: bool,
    supports_unseal: bool,
    supports_sealing_public: bool,
    supports_rotate_context_handle: bool,
    dice_derivation: String,
    asymmetric_derivation: String,
    symmetric_derivation: String,
    supports_any_label: bool,
    supported_labels: String,
    initial_derivation: String,
    input_format: String,
    supports_internal_inputs: bool,
    supports_internal_dpe_info: bool,
    supports_internal_dpe_dice: bool,
    internal_dpe_info_type: String,
    internal_dpe_dice_type: String,
    internal_inputs: String,
    supports_certificates: bool,
    max_certificate_size: usize,
    max_certificate_chain_size: usize,
    appends_more_certificates: bool,
    supports_certificate_policies: bool,
    supports_policy_identity_init: bool,
    supports_policy_identity_loc: bool,
    supports_policy_attest_init: bool,
    supports_policy_attest_loc: bool,
    supports_policy_assert_init: bool,
    supports_policy_assert_loc: bool,
    certificate_policies: String,
    supports_eca_certificates: bool,
    eca_certificate_format: String,
    leaf_certificate_format: String,
    public_key_format: String,
    supports_external_key: bool,
    to_be_signed_format: String,
    signature_format: String,
    supports_symmetric_sign: bool,
    supports_asymmetric_unseal: bool,
    supports_unseal_policy: bool,
    unseal_policy_format: String,
) -> profile_descriptor_t {
    profile_descriptor_t {
        name: name,
        dpe_spec_version: dpe_spec_version,
        max_message_size: max_message_size,
        uses_multi_part_messages: uses_multi_part_messages,
        supports_concurrent_operations: supports_concurrent_operations,
        supports_encrypted_sessions: supports_encrypted_sessions,
        supports_derived_sessions: supports_derived_sessions,
        max_sessions: max_sessions,
        session_protocol: session_protocol,
        supports_session_sync: supports_session_sync,
        session_sync_policy: session_sync_policy,
        session_migration_protocol: session_migration_protocol,
        supports_default_context: supports_default_context,
        supports_context_handles: supports_context_handles,
        max_contexts_per_session: max_contexts_per_session,
        max_context_handle_size: max_context_handle_size,
        supports_auto_init: supports_auto_init,
        supports_simulation: supports_simulation,
        supports_attestation: supports_attestation,
        supports_sealing: supports_sealing,
        supports_get_profile: supports_get_profile,
        supports_open_session: supports_open_session,
        supports_close_session: supports_close_session,
        supports_sync_session: supports_sync_session,
        supports_export_session: supports_export_session,
        supports_import_session: supports_import_session,
        supports_init_context: supports_init_context,
        supports_certify_key: supports_certify_key,
        supports_sign: supports_sign,
        supports_seal: supports_seal,
        supports_unseal: supports_unseal,
        supports_sealing_public: supports_sealing_public,
        supports_rotate_context_handle: supports_rotate_context_handle,
        dice_derivation: dice_derivation,
        asymmetric_derivation: asymmetric_derivation,
        symmetric_derivation: symmetric_derivation,
        supports_any_label: supports_any_label,
        supported_labels: supported_labels,
        initial_derivation: initial_derivation,
        input_format: input_format,
        supports_internal_inputs: supports_internal_inputs,
        supports_internal_dpe_info: supports_internal_dpe_info,
        supports_internal_dpe_dice: supports_internal_dpe_dice,
        internal_dpe_info_type: internal_dpe_info_type,
        internal_dpe_dice_type: internal_dpe_dice_type,
        internal_inputs: internal_inputs,
        supports_certificates: supports_certificates,
        max_certificate_size: max_certificate_size,
        max_certificate_chain_size: max_certificate_chain_size,
        appends_more_certificates: appends_more_certificates,
        supports_certificate_policies: supports_certificate_policies,
        supports_policy_identity_init: supports_policy_identity_init,
        supports_policy_identity_loc: supports_policy_identity_loc,
        supports_policy_attest_init: supports_policy_attest_init,
        supports_policy_attest_loc: supports_policy_attest_loc,
        supports_policy_assert_init: supports_policy_assert_init,
        supports_policy_assert_loc: supports_policy_assert_loc,
        certificate_policies: certificate_policies,
        supports_eca_certificates: supports_eca_certificates,
        eca_certificate_format: eca_certificate_format,
        leaf_certificate_format: leaf_certificate_format,
        public_key_format: public_key_format,
        supports_external_key: supports_external_key,
        to_be_signed_format: to_be_signed_format,
        signature_format: signature_format,
        supports_symmetric_sign: supports_symmetric_sign,
        supports_asymmetric_unseal: supports_asymmetric_unseal,
        supports_unseal_policy: supports_unseal_policy,
        unseal_policy_format: unseal_policy_format,
    }
}

#[derive(Clone)]
pub struct engine_context_t {
    uds: std::vec::Vec<u8>,
}
pub fn mk_engine_context_t(uds: std::vec::Vec<u8>) -> engine_context_t {
    engine_context_t { uds: uds }
}

#[derive(Clone)]
pub struct l0_context_t {
    cdi: std::vec::Vec<u8>,
}
pub fn mk_l0_context_t(cdi: std::vec::Vec<u8>) -> l0_context_t {
    l0_context_t { cdi: cdi }
}

#[derive(Clone)]
pub struct l1_context_t {
    deviceID_priv: std::vec::Vec<u8>,
    deviceID_pub: std::vec::Vec<u8>,
    aliasKey_priv: std::vec::Vec<u8>,
    aliasKey_pub: std::vec::Vec<u8>,
    aliasKeyCRT: std::vec::Vec<u8>,
    deviceIDCSR: std::vec::Vec<u8>,
}
pub fn mk_l1_context_t(
    deviceID_priv: std::vec::Vec<u8>,
    deviceID_pub: std::vec::Vec<u8>,
    aliasKey_priv: std::vec::Vec<u8>,
    aliasKey_pub: std::vec::Vec<u8>,
    aliasKeyCRT: std::vec::Vec<u8>,
    deviceIDCSR: std::vec::Vec<u8>,
) -> l1_context_t {
    l1_context_t {
        deviceID_priv: deviceID_priv,
        deviceID_pub: deviceID_pub,
        aliasKey_priv: aliasKey_priv,
        aliasKey_pub: aliasKey_pub,
        aliasKeyCRT: aliasKeyCRT,
        deviceIDCSR: deviceIDCSR,
    }
}

#[derive(Clone)]
pub enum context_t {
    Engine_context(engine_context_t),
    L0_context(l0_context_t),
    L1_context(l1_context_t),
}
use crate::context_t::*;
pub fn mk_context_t_engine(c: engine_context_t) -> context_t {
    context_t::Engine_context(c)
}
pub fn mk_context_t_l0(c: l0_context_t) -> context_t {
    context_t::L0_context(c)
}
pub fn mk_context_t_l1(c: l1_context_t) -> context_t {
    context_t::L1_context(c)
}
pub enum record_t {
    Engine_record(engine_record_t),
    L0_record(l0_record_t),
}
use crate::record_t::*;
#[derive(Clone)]
pub enum cell<KT: PartialEq + Copy + Clone, VT: Clone> {
    Clean,
    Zombie,
    Used(KT, VT),
}
use crate::cell::*;
pub type pos_us = usize;
pub struct ht_t<KEYT: Copy + PartialEq + Clone, VALT: Clone> {
    sz: pos_us,
    hashf: fn(KEYT) -> usize,
    contents: std::vec::Vec<cell<KEYT, VALT>>,
}
pub fn mk_used_cell<A: Copy + PartialEq + Clone, B: Clone>(k: A, v: B) -> cell<A, B> {
    cell::Used(k, v)
}
pub fn mk_ht<K: Copy + PartialEq + Clone, V: Clone>(
    sz: pos_us,
    hashf: fn(K) -> usize,
    contents: std::vec::Vec<cell<K, V>>,
) -> ht_t<K, V> {
    ht_t {
        sz: sz,
        hashf: hashf,
        contents: contents,
    }
}
pub fn alloc<K: Copy + PartialEq + Clone, V: Clone>(
    hashf: fn(K) -> usize,
    l: pos_us,
) -> ht_t<K, V> {
    let mut contents = vec![cell::Clean; l];
    let ht = mk_ht(l, hashf, contents);
    ht
}
pub fn sz_add(x: usize, y: usize) -> std::option::Option<usize> {
    match x <= 0xffff {
        true => match y <= 0xffff - x {
            true => Some(x + y),
            _ => None,
        },
        _ => None,
    }
}
pub fn size_t_mod(x: usize, y: usize) -> usize {
    x % y
}
pub fn replace<KT: Copy + PartialEq + Clone, VT: Clone>(
    pht: (),
    ht: ht_t<KT, VT>,
    idx: usize,
    k: KT,
    v: VT,
    uu___: (),
) -> (ht_t<KT, VT>, VT) {
    let hashf = ht.hashf;
    let mut contents = ht.contents;
    let v_ = std::mem::replace(&mut contents[idx], mk_used_cell(k, v));
    let vcontents = contents;
    let ht1 = mk_ht(ht.sz, hashf, vcontents);
    let _bind_c = match v_ {
        Used(k_, v_1) => {
            let res = (ht1, v_1);
            res
        }
        Used(k_, v_1) => {
            let res = (ht1, v_1);
            res
        }
        Clean => panic!(),
        Zombie => panic!(),
    };
    let contents1 = _bind_c;
    contents1
}
pub fn lookup<KT: Copy + PartialEq + Clone, VT: Clone>(
    pht: (),
    ht: ht_t<KT, VT>,
    k: KT,
) -> (ht_t<KT, VT>, bool, std::option::Option<usize>) {
    let hashf = ht.hashf;
    let mut contents = ht.contents;
    let cidx = size_t_mod(hashf(k), ht.sz);
    let mut off = 0;
    let mut cont = true;
    let mut err = false;
    let mut ret = None;
    while {
        let voff = off;
        let vcont = cont;
        let verr = err;
        voff <= ht.sz && vcont == true && verr == false
    } {
        let voff = off;
        if voff == ht.sz {
            cont = false;
        } else {
            let opt_sum = sz_add(cidx, voff);
            match opt_sum {
                Some(sum) => {
                    let idx = size_t_mod(sum, ht.sz);
                    let c = std::mem::replace(&mut contents[idx], cell::Zombie);
                    match c {
                        Used(k_, v_) => {
                            if k_ == k {
                                cont = false;
                                ret = Some(idx);
                                let uu___2 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            } else {
                                off = voff + 1;
                                let uu___1 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            }
                        }
                        Used(k_, v_) => {
                            if k_ == k {
                                cont = false;
                                ret = Some(idx);
                                let uu___2 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            } else {
                                off = voff + 1;
                                let uu___1 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            }
                        }
                        Clean => {
                            cont = false;
                            let uu___1 = std::mem::replace(&mut contents[idx], c);
                        }
                        Zombie => {
                            off = voff + 1;
                            let uu___1 = std::mem::replace(&mut contents[idx], c);
                        }
                    }
                }
                Some(sum) => {
                    let idx = size_t_mod(sum, ht.sz);
                    let c = std::mem::replace(&mut contents[idx], cell::Zombie);
                    match c {
                        Used(k_, v_) => {
                            if k_ == k {
                                cont = false;
                                ret = Some(idx);
                                let uu___2 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            } else {
                                off = voff + 1;
                                let uu___1 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            }
                        }
                        Used(k_, v_) => {
                            if k_ == k {
                                cont = false;
                                ret = Some(idx);
                                let uu___2 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            } else {
                                off = voff + 1;
                                let uu___1 =
                                    std::mem::replace(&mut contents[idx], cell::Used(k_, v_));
                            }
                        }
                        Clean => {
                            cont = false;
                            let uu___1 = std::mem::replace(&mut contents[idx], c);
                        }
                        Zombie => {
                            off = voff + 1;
                            let uu___1 = std::mem::replace(&mut contents[idx], c);
                        }
                    }
                }
                None => err = true,
            }
        };
    }
    let verr = err;
    let o = ret;
    let vcontents = contents;
    let ht1 = mk_ht(ht.sz, ht.hashf, vcontents);
    let _bind_c = if verr {
        let res = (ht1, false, o);
        res
    } else {
        let res = (ht1, true, o);
        res
    };
    let ret1 = _bind_c;
    let err1 = ret1;
    let cont1 = err1;
    let off1 = cont1;
    let contents1 = off1;
    contents1
}
pub fn insert<KT: Copy + PartialEq + Clone, VT: Clone>(
    ht: ht_t<KT, VT>,
    k: KT,
    v: VT,
    pht: (),
) -> (ht_t<KT, VT>, bool) {
    let hashf = ht.hashf;
    let mut contents = ht.contents;
    let cidx = size_t_mod(hashf(k), ht.sz);
    let mut off = 0;
    let mut cont = true;
    let mut err = false;
    let mut idx = 0;
    while {
        let vcont = cont;
        let verr = err;
        vcont == true && verr == false
    } {
        let voff = off;
        if voff == ht.sz {
            cont = false;
        } else {
            let opt_sum = sz_add(cidx, voff);
            match opt_sum {
                Some(sum) => {
                    let vidx = size_t_mod(sum, ht.sz);
                    let c = std::mem::replace(&mut contents[vidx], cell::Zombie);
                    match c {
                        Used(k_, v_) => {
                            if k_ == k {
                                contents[vidx] = cell::Used(k_, v_);
                                cont = false;
                                idx = vidx;
                            } else {
                                contents[vidx] = cell::Used(k_, v_);
                                off = voff + 1
                            }
                        }
                        Used(k_, v_) => {
                            if k_ == k {
                                contents[vidx] = cell::Used(k_, v_);
                                cont = false;
                                idx = vidx;
                            } else {
                                contents[vidx] = cell::Used(k_, v_);
                                off = voff + 1
                            }
                        }
                        Clean => {
                            contents[vidx] = cell::Clean;
                            cont = false;
                            idx = vidx;
                        }
                        Zombie => {
                            let vcontents = contents;
                            let ht1 = ht_t {
                                sz: ht.sz,
                                hashf: hashf,
                                contents: vcontents,
                            };
                            let res = lookup((), ht1, k);
                            contents = res.0.contents;
                            if res.1 {
                                let o = res.2;
                                match o {
                                    Some(p) => {
                                        contents[p] = cell::Zombie;
                                        cont = false;
                                        idx = vidx;
                                    }
                                    Some(p) => {
                                        contents[p] = cell::Zombie;
                                        cont = false;
                                        idx = vidx;
                                    }
                                    None => {
                                        cont = false;
                                        idx = vidx;
                                    }
                                }
                            } else {
                                err = true
                            }
                        }
                    }
                }
                Some(sum) => {
                    let vidx = size_t_mod(sum, ht.sz);
                    let c = std::mem::replace(&mut contents[vidx], cell::Zombie);
                    match c {
                        Used(k_, v_) => {
                            if k_ == k {
                                contents[vidx] = cell::Used(k_, v_);
                                cont = false;
                                idx = vidx;
                            } else {
                                contents[vidx] = cell::Used(k_, v_);
                                off = voff + 1
                            }
                        }
                        Used(k_, v_) => {
                            if k_ == k {
                                contents[vidx] = cell::Used(k_, v_);
                                cont = false;
                                idx = vidx;
                            } else {
                                contents[vidx] = cell::Used(k_, v_);
                                off = voff + 1
                            }
                        }
                        Clean => {
                            contents[vidx] = cell::Clean;
                            cont = false;
                            idx = vidx;
                        }
                        Zombie => {
                            let vcontents = contents;
                            let ht1 = ht_t {
                                sz: ht.sz,
                                hashf: hashf,
                                contents: vcontents,
                            };
                            let res = lookup((), ht1, k);
                            contents = res.0.contents;
                            if res.1 {
                                let o = res.2;
                                match o {
                                    Some(p) => {
                                        contents[p] = cell::Zombie;
                                        cont = false;
                                        idx = vidx;
                                    }
                                    Some(p) => {
                                        contents[p] = cell::Zombie;
                                        cont = false;
                                        idx = vidx;
                                    }
                                    None => {
                                        cont = false;
                                        idx = vidx;
                                    }
                                }
                            } else {
                                err = true
                            }
                        }
                    }
                }
                None => err = true,
            }
        };
    }
    let vcont = cont;
    let verr = err;
    let vidx = idx;
    let _bind_c = if vcont == false && verr == false {
        contents[vidx] = mk_used_cell(k, v);
        let vcontents = contents;
        let ht1 = mk_ht(ht.sz, hashf, vcontents);
        let res = (ht1, true);
        res
    } else {
        let vcontents = contents;
        let ht1 = mk_ht(ht.sz, hashf, vcontents);
        let res = (ht1, false);
        res
    };
    let idx1 = _bind_c;
    let err1 = idx1;
    let cont1 = err1;
    let off1 = cont1;
    let contents1 = off1;
    contents1
}
pub fn is_used<K: Copy + PartialEq + Clone, V: Clone>(c: cell<K, V>) -> (bool, cell<K, V>) {
    match c {
        Used(_, _) => (true, c),
        _ => (false, c),
    }
}
pub fn not_full<KT: Copy + PartialEq + Clone, VT: Clone>(
    ht: ht_t<KT, VT>,
    pht: (),
) -> (ht_t<KT, VT>, bool) {
    let hashf = ht.hashf;
    let mut contents = ht.contents;
    let mut i = 0;
    while {
        let vi = i;
        if vi < ht.sz {
            let c = std::mem::replace(&mut contents[vi], cell::Zombie);
            let b = is_used(c);
            let uu___ = std::mem::replace(&mut contents[vi], b.1);
            b.0
        } else {
            false
        }
    } {
        let vi = i;
        i = vi + 1;
    }
    let vi = i;
    let res = vi < ht.sz;
    let vcontents = contents;
    let ht1 = mk_ht(ht.sz, hashf, vcontents);
    let b = (ht1, res);
    let i1 = b;
    let contents1 = i1;
    contents1
}
pub fn run_stt<A>(post: (), f: A) -> A {
    panic!()
}
pub type ctxt_hndl_t = u32;
pub type sid_t = u32;
#[derive(Clone)]
pub struct session_state__Available__payload {
    handle: ctxt_hndl_t,
    context: context_t,
}
#[derive(Clone)]
pub enum session_state {
    SessionStart,
    Available(session_state__Available__payload),
    InUse,
    SessionClosed,
    SessionError,
}
use crate::session_state::*;
pub fn mk_available_payload(
    handle: ctxt_hndl_t,
    context: context_t,
) -> session_state__Available__payload {
    session_state__Available__payload {
        handle: handle,
        context: context,
    }
}
pub fn intro_session_state_perm_available(
    ctxt: context_t,
    hndl: ctxt_hndl_t,
    __repr: (),
) -> session_state {
    session_state::Available(mk_available_payload(hndl, ctxt))
}
pub struct global_state_t {
    session_id_counter: sid_t,
    session_table: ht_t<sid_t, session_state>,
}
pub fn sid_hash(uu___: sid_t) -> usize {
    panic!()
}
pub const fn initialize_global_state(
    uu___: (),
) -> std::sync::Mutex<std::option::Option<global_state_t>> {
    let res = None;
    std::sync::Mutex::new(res)
}
pub static global_state: std::sync::Mutex<std::option::Option<global_state_t>> =
    initialize_global_state(());
pub fn mk_global_state(uu___: ()) -> global_state_t {
    let session_table = alloc(sid_hash, 256);
    let st = global_state_t {
        session_id_counter: 0,
        session_table: session_table,
    };
    st
}
pub fn insert_if_not_full<KT: Copy + PartialEq + Clone, VT: Clone>(
    ht: ht_t<KT, VT>,
    k: KT,
    v: VT,
    pht: (),
) -> (ht_t<KT, VT>, bool) {
    let b = not_full(ht, ());
    if b.1 {
        insert(b.0, k, v, ())
    } else {
        let res = (b.0, false);
        res
    }
}
pub fn safe_add(i: u32, j: u32) -> std::option::Option<u32> {
    panic!()
}
pub fn open_session_aux(st: global_state_t) -> (global_state_t, std::option::Option<sid_t>) {
    let ctr = st.session_id_counter;
    let tbl = st.session_table;
    let opt_inc = safe_add(ctr, 1);
    match opt_inc {
        None => {
            let st1 = global_state_t {
                session_id_counter: ctr,
                session_table: tbl,
            };
            let res = (st1, None);
            res
        }
        None => {
            let st1 = global_state_t {
                session_id_counter: ctr,
                session_table: tbl,
            };
            let res = (st1, None);
            res
        }
        Some(next_sid) => {
            let res = insert_if_not_full(tbl, ctr, session_state::SessionStart, ());
            if res.1 {
                let st1 = global_state_t {
                    session_id_counter: next_sid,
                    session_table: res.0,
                };
                let res1 = (st1, Some(next_sid));
                res1
            } else {
                let st1 = global_state_t {
                    session_id_counter: ctr,
                    session_table: res.0,
                };
                let res1 = (st1, None);
                res1
            }
        }
    }
}
pub fn destroy_ctxt(ctxt: context_t, repr: ()) -> () {
    match ctxt {
        Engine_context(c) => drop(c.uds),
        Engine_context(c) => drop(c.uds),
        L0_context(c) => drop(c.cdi),
        L1_context(c) => {
            drop(c.deviceID_priv);
            drop(c.deviceID_pub);
            drop(c.aliasKey_priv);
            drop(c.aliasKey_pub);
            drop(c.aliasKeyCRT);
            drop(c.deviceIDCSR)
        }
    }
}
pub fn take_session_state(
    sid: sid_t,
    replace_with: session_state,
) -> std::option::Option<session_state> {
    let r: &mut std::option::Option<global_state_t> = &mut global_state.lock().unwrap();
    let st_opt = std::mem::replace(r, None);
    match st_opt {
        None => None,
        None => None,
        Some(st) => {
            let ctr = st.session_id_counter;
            let tbl = st.session_table;
            if sid < ctr {
                let ss = lookup((), tbl, sid);
                if ss.1 {
                    match ss.2 {
                        Some(idx) => {
                            let ok = replace((), ss.0, idx, sid, replace_with, ());
                            let st1 = global_state_t {
                                session_id_counter: ctr,
                                session_table: ok.0,
                            };
                            *r = Some(st1);
                            Some(ok.1)
                        }
                        Some(idx) => {
                            let ok = replace((), ss.0, idx, sid, replace_with, ());
                            let st1 = global_state_t {
                                session_id_counter: ctr,
                                session_table: ok.0,
                            };
                            *r = Some(st1);
                            Some(ok.1)
                        }
                        None => {
                            let st1 = global_state_t {
                                session_id_counter: ctr,
                                session_table: ss.0,
                            };
                            *r = Some(st1);
                            None
                        }
                    }
                } else {
                    let st1 = global_state_t {
                        session_id_counter: ctr,
                        session_table: ss.0,
                    };
                    *r = Some(st1);
                    None
                }
            } else {
                let st1 = global_state_t {
                    session_id_counter: ctr,
                    session_table: tbl,
                };
                *r = Some(st1);
                None
            }
        }
    }
}
pub fn destroy_session_state(st: session_state) -> () {
    match st {
        Available(st1) => destroy_ctxt(st1.context, ()),
        Available(st1) => destroy_ctxt(st1.context, ()),
        _ => (),
    }
}
pub fn init_engine_ctxt(uds: &mut [u8], p: (), uds_bytes: ()) -> context_t {
    let mut uds_buf = vec![0; uds_len];
    memcpy(uds_len, uds, &mut uds_buf, (), (), ());
    let engine_context = mk_engine_context_t(uds_buf);
    let ctxt = mk_context_t_engine(engine_context);
    ctxt
}
pub fn init_l0_ctxt(cdi: &mut [u8], engine_repr: (), s: (), uds_bytes: (), uu___: ()) -> context_t {
    let mut cdi_buf = vec![0; dice_digest_len];
    memcpy(dice_digest_len, cdi, &mut cdi_buf, (), (), ());
    let l0_context = mk_l0_context_t(cdi_buf);
    let ctxt = mk_context_t_l0(l0_context);
    ctxt
}
pub fn init_l1_ctxt(
    deviceIDCSR_len: usize,
    aliasKeyCRT_len: usize,
    deviceID_priv: &mut [u8],
    deviceID_pub: &mut [u8],
    aliasKey_priv: &mut [u8],
    aliasKey_pub: &mut [u8],
    deviceIDCSR: &mut [u8],
    aliasKeyCRT: &mut [u8],
    deviceID_label_len: (),
    aliasKey_label_len: (),
    cdi: (),
    repr: (),
    deviceIDCSR_ingredients: (),
    aliasKeyCRT_ingredients: (),
    deviceID_priv0: (),
    deviceID_pub0: (),
    aliasKey_priv0: (),
    aliasKey_pub0: (),
    deviceIDCSR0: (),
    aliasKeyCRT0: (),
) -> context_t {
    let mut deviceID_pub_buf = vec![0; v32us];
    let mut deviceID_priv_buf = vec![0; v32us];
    let mut aliasKey_priv_buf = vec![0; v32us];
    let mut aliasKey_pub_buf = vec![0; v32us];
    let mut deviceIDCSR_buf = vec![0; deviceIDCSR_len];
    let mut aliasKeyCRT_buf = vec![0; aliasKeyCRT_len];
    memcpy(v32us, deviceID_priv, &mut deviceID_priv_buf, (), (), ());
    memcpy(v32us, deviceID_pub, &mut deviceID_pub_buf, (), (), ());
    memcpy(v32us, aliasKey_priv, &mut aliasKey_priv_buf, (), (), ());
    memcpy(v32us, aliasKey_pub, &mut aliasKey_pub_buf, (), (), ());
    memcpy(
        deviceIDCSR_len,
        deviceIDCSR,
        &mut deviceIDCSR_buf,
        (),
        (),
        (),
    );
    memcpy(
        aliasKeyCRT_len,
        aliasKeyCRT,
        &mut aliasKeyCRT_buf,
        (),
        (),
        (),
    );
    let l1_context = mk_l1_context_t(
        deviceID_priv_buf,
        deviceID_pub_buf,
        aliasKey_priv_buf,
        aliasKey_pub_buf,
        aliasKeyCRT_buf,
        deviceIDCSR_buf,
    );
    let ctxt = mk_context_t_l1(l1_context);
    ctxt
}
pub fn prng(uu___: ()) -> u32 {
    panic!()
}
pub fn intro_maybe_context_perm(c: context_t, __repr: ()) -> std::option::Option<context_t> {
    Some(c)
}
pub fn derive_child_from_context(
    context: context_t,
    record: record_t,
    p: (),
    record_repr: (),
    context_repr: (),
) -> (context_t, record_t, std::option::Option<context_t>) {
    match context {
        Engine_context(c) => {
            if op_Negation(uu___is_Engine_record(record)) {
                let res = (context, record, None);
                res
            } else {
                match record {
                    Engine_record(r) => {
                        let cdi = &mut [0; dice_digest_len];
                        let ret = engine_main(cdi, &mut c.uds, r, (), (), (), (), ());
                        let _bind_c = match ret.1 {
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_ERROR => {
                                zeroize(dice_digest_len, cdi, ());
                                let res = (context, record_t::Engine_record(ret.0), None);
                                res
                            }
                        };
                        let cdi1 = _bind_c;
                        cdi1
                    }
                    Engine_record(r) => {
                        let cdi = &mut [0; dice_digest_len];
                        let ret = engine_main(cdi, &mut c.uds, r, (), (), (), (), ());
                        let _bind_c = match ret.1 {
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_ERROR => {
                                zeroize(dice_digest_len, cdi, ());
                                let res = (context, record_t::Engine_record(ret.0), None);
                                res
                            }
                        };
                        let cdi1 = _bind_c;
                        cdi1
                    }
                }
            }
        }
        Engine_context(c) => {
            if op_Negation(uu___is_Engine_record(record)) {
                let res = (context, record, None);
                res
            } else {
                match record {
                    Engine_record(r) => {
                        let cdi = &mut [0; dice_digest_len];
                        let ret = engine_main(cdi, &mut c.uds, r, (), (), (), (), ());
                        let _bind_c = match ret.1 {
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_ERROR => {
                                zeroize(dice_digest_len, cdi, ());
                                let res = (context, record_t::Engine_record(ret.0), None);
                                res
                            }
                        };
                        let cdi1 = _bind_c;
                        cdi1
                    }
                    Engine_record(r) => {
                        let cdi = &mut [0; dice_digest_len];
                        let ret = engine_main(cdi, &mut c.uds, r, (), (), (), (), ());
                        let _bind_c = match ret.1 {
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_SUCCESS => {
                                let l0_ctxt = init_l0_ctxt(cdi, (), (), (), ());
                                let l0_ctxt_opt = intro_maybe_context_perm(l0_ctxt, ());
                                let res = (context, record_t::Engine_record(ret.0), l0_ctxt_opt);
                                res
                            }
                            DICE_ERROR => {
                                zeroize(dice_digest_len, cdi, ());
                                let res = (context, record_t::Engine_record(ret.0), None);
                                res
                            }
                        };
                        let cdi1 = _bind_c;
                        cdi1
                    }
                }
            }
        }
        L0_context(c) => {
            if op_Negation(uu___is_L0_record(record)) {
                let res = (context, record, None);
                res
            } else {
                match record {
                    L0_record(r) => {
                        let idcsr_ing = r.deviceIDCSR_ingredients;
                        let akcrt_ing = r.aliasKeyCRT_ingredients;
                        let deviceIDCRI_len = len_of_deviceIDCRI(
                            idcsr_ing.version,
                            idcsr_ing.s_common,
                            idcsr_ing.s_org,
                            idcsr_ing.s_country,
                        );
                        let aliasKeyTBS_len = len_of_aliasKeyTBS(
                            akcrt_ing.serialNumber,
                            akcrt_ing.i_common,
                            akcrt_ing.i_org,
                            akcrt_ing.i_country,
                            akcrt_ing.s_common1,
                            akcrt_ing.s_org1,
                            akcrt_ing.s_country1,
                            akcrt_ing.l0_version,
                        );
                        let deviceIDCSR_len = length_of_deviceIDCSR(deviceIDCRI_len);
                        let aliasKeyCRT_len = length_of_aliasKeyCRT(aliasKeyTBS_len);
                        let deviceID_pub = &mut [0; v32us];
                        let deviceID_priv = &mut [0; v32us];
                        let aliasKey_pub = &mut [0; v32us];
                        let aliasKey_priv = &mut [0; v32us];
                        let deviceIDCSR = &mut [0; deviceIDCSR_len];
                        let aliasKeyCRT = &mut [0; aliasKeyCRT_len];
                        l0_main(
                            &mut c.cdi,
                            deviceID_pub,
                            deviceID_priv,
                            aliasKey_pub,
                            aliasKey_priv,
                            aliasKeyTBS_len,
                            aliasKeyCRT_len,
                            aliasKeyCRT,
                            deviceIDCRI_len,
                            deviceIDCSR_len,
                            deviceIDCSR,
                            r,
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                        );
                        let l1_context = init_l1_ctxt(
                            deviceIDCSR_len,
                            aliasKeyCRT_len,
                            deviceID_priv,
                            deviceID_pub,
                            aliasKey_priv,
                            aliasKey_pub,
                            deviceIDCSR,
                            aliasKeyCRT,
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                        );
                        let l1_context_opt = intro_maybe_context_perm(l1_context, ());
                        let res = (context, record, l1_context_opt);
                        let aliasKeyCRT1 = res;
                        let deviceIDCSR1 = aliasKeyCRT1;
                        let aliasKey_priv1 = deviceIDCSR1;
                        let aliasKey_pub1 = aliasKey_priv1;
                        let deviceID_priv1 = aliasKey_pub1;
                        let deviceID_pub1 = deviceID_priv1;
                        deviceID_pub1
                    }
                    L0_record(r) => {
                        let idcsr_ing = r.deviceIDCSR_ingredients;
                        let akcrt_ing = r.aliasKeyCRT_ingredients;
                        let deviceIDCRI_len = len_of_deviceIDCRI(
                            idcsr_ing.version,
                            idcsr_ing.s_common,
                            idcsr_ing.s_org,
                            idcsr_ing.s_country,
                        );
                        let aliasKeyTBS_len = len_of_aliasKeyTBS(
                            akcrt_ing.serialNumber,
                            akcrt_ing.i_common,
                            akcrt_ing.i_org,
                            akcrt_ing.i_country,
                            akcrt_ing.s_common1,
                            akcrt_ing.s_org1,
                            akcrt_ing.s_country1,
                            akcrt_ing.l0_version,
                        );
                        let deviceIDCSR_len = length_of_deviceIDCSR(deviceIDCRI_len);
                        let aliasKeyCRT_len = length_of_aliasKeyCRT(aliasKeyTBS_len);
                        let deviceID_pub = &mut [0; v32us];
                        let deviceID_priv = &mut [0; v32us];
                        let aliasKey_pub = &mut [0; v32us];
                        let aliasKey_priv = &mut [0; v32us];
                        let deviceIDCSR = &mut [0; deviceIDCSR_len];
                        let aliasKeyCRT = &mut [0; aliasKeyCRT_len];
                        l0_main(
                            &mut c.cdi,
                            deviceID_pub,
                            deviceID_priv,
                            aliasKey_pub,
                            aliasKey_priv,
                            aliasKeyTBS_len,
                            aliasKeyCRT_len,
                            aliasKeyCRT,
                            deviceIDCRI_len,
                            deviceIDCSR_len,
                            deviceIDCSR,
                            r,
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                        );
                        let l1_context = init_l1_ctxt(
                            deviceIDCSR_len,
                            aliasKeyCRT_len,
                            deviceID_priv,
                            deviceID_pub,
                            aliasKey_priv,
                            aliasKey_pub,
                            deviceIDCSR,
                            aliasKeyCRT,
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                            (),
                        );
                        let l1_context_opt = intro_maybe_context_perm(l1_context, ());
                        let res = (context, record, l1_context_opt);
                        let aliasKeyCRT1 = res;
                        let deviceIDCSR1 = aliasKeyCRT1;
                        let aliasKey_priv1 = deviceIDCSR1;
                        let aliasKey_pub1 = aliasKey_priv1;
                        let deviceID_priv1 = aliasKey_pub1;
                        let deviceID_pub1 = deviceID_priv1;
                        deviceID_pub1
                    }
                }
            }
        }
        L1_context(_) => {
            let res = (context, record, None);
            res
        }
    }
}
