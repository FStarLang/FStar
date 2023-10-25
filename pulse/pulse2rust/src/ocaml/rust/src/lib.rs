use ocaml_interop::{
    impl_from_ocaml_record, impl_from_ocaml_variant, ocaml_export, OCaml, OCamlList, OCamlRef,
    ToOCaml,
};
use proc_macro2::Span;
use syn::{
    punctuated::Punctuated, token::Brace, token::Colon, token::Comma, token::Eq, token::Let,
    token::Mut, token::Paren, token::Pub, token::RArrow, token::Ref, token::Semi, Block, Generics,
    Ident, ItemFn, Local, LocalInit, Pat as SynPat, PatType, Path, PathArguments, PathSegment,
    ReturnType, Signature, Type, TypePath, Visibility,
};

use std::fmt;

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
}

enum BinOp {
    Add,
    Sub,
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

enum Expr {
    EBinOp(ExprBin),
    EPath(String),
    ECall(ExprCall),
    EUnOp(ExprUnary),
    EAssign(ExprAssign),
    EBlock(Vec<Stmt>),
    ELit(Lit),
    EIf(ExprIf),
    EWhile(ExprWhile),
}

struct TypeReference {
    type_reference_mut: bool,
    type_reference_typ: Box<Typ>,
}

enum Typ {
    TName(String),
    TReference(TypeReference),
}

struct PatIdent {
    pat_name: String,
    by_ref: bool,
    is_mut: bool,
}

enum Pat {
    PIdent(PatIdent),
}

struct LocalStmt {
    local_stmt_pat: Pat,
    local_stmt_init: Option<Expr>,
}

enum Stmt {
    SLocal(LocalStmt),
    SExpr(Expr),
}

enum GenericParam {
    GenericTypeParam(String),
}

struct PatTyp {
    pat_typ_pat: Pat,
    pat_typ_typ: Typ,
}

enum FnArg {
    FnArgPat(PatTyp),
}

struct FnSig {
    fn_name: String,
    fn_generics: Vec<GenericParam>,
    fn_args: Vec<FnArg>,
    fn_ret_t: Typ,
}

struct Fn {
    fn_sig: FnSig,
    fn_body: Vec<Stmt>,
}

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
  }
}

impl_from_ocaml_variant! {
  BinOp {
      BinOp::Add,
      BinOp::Sub,
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
    Expr::EPath (payload:String),
    Expr::ECall (payload:ExprCall),
    Expr::EUnOp (payload:ExprUnary),
    Expr::EAssign (payload:ExprAssign),
    Expr::EBlock (payload:OCamlList<Stmt>),
    Expr::ELit (payload:Lit),
    Expr::EIf (payload:ExprIf),
    Expr::EWhile (payload:ExprWhile)
  }
}

impl_from_ocaml_record! {
  ExprCall {
    call_fn : Expr,
    call_args : OCamlList<Expr>
  }
}

impl_from_ocaml_record! {
  ExprBin {
    expr_bin_left : Expr,
    op : BinOp,
    expr_bin_right : Expr,
  }
}

impl_from_ocaml_record! {
  ExprUnary {
    expr_unary_op : UnOp,
    expr_unary_expr : Expr,
  }
}

impl_from_ocaml_record! {
  ExprAssign {
    expr_assign_l : Expr,
    expr_assign_r : Expr,
  }
}

impl_from_ocaml_record! {
  ExprIf {
    expr_if_cond : Expr,
    expr_if_then : OCamlList<Stmt>,
    expr_if_else : Option<Expr>
  }
}

impl_from_ocaml_record! {
  ExprWhile {
    expr_while_cond : Expr,
    expr_while_body : OCamlList<Stmt>,
  }
}

impl_from_ocaml_record! {
  TypeReference {
    type_reference_mut : bool,
    type_reference_typ : Typ,
  }
}

impl_from_ocaml_variant! {
  Typ {
    Typ::TName (payload:String),
    Typ::TReference (payload:TypeReference),
  }
}

impl_from_ocaml_record! {
  PatIdent {
    pat_name : String,
    by_ref : bool,
    is_mut : bool,
  }
}

impl_from_ocaml_variant! {
  Pat {
    Pat::PIdent (payload:PatIdent),
  }
}

impl_from_ocaml_record! {
  LocalStmt {
    local_stmt_pat : Pat,
    local_stmt_init : Option<Expr>,
  }
}

impl_from_ocaml_variant! {
  Stmt {
    Stmt::SLocal (payload:LocalStmt),
    Stmt::SExpr (payload:Expr),
  }
}

impl_from_ocaml_variant! {
  GenericParam {
    GenericParam::GenericTypeParam (payload:String),
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

fn to_syn_path(s: String) -> syn::Path {
    let mut segs: Punctuated<syn::PathSegment, syn::token::PathSep> = Punctuated::new();
    segs.push(PathSegment {
        ident: Ident::new(&s, Span::call_site()),
        arguments: PathArguments::None,
    });
    Path {
        leading_colon: None,
        segments: segs,
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
                op: match e.op {
                    BinOp::Add => syn::BinOp::Add(syn::token::Plus {
                        spans: [Span::call_site()],
                    }),
                    BinOp::Sub => syn::BinOp::Sub(syn::token::Minus {
                        spans: [Span::call_site()],
                    }),
                },
                right: Box::new(e2),
            })
        }
        Expr::EPath(s) => {
            let path = to_syn_path(s.to_string());
            syn::Expr::Path(syn::ExprPath {
                attrs: vec![],
                qself: None,
                path,
            })
        }
        Expr::ECall(e) => {
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
            Lit::LitInt(LitInt { lit_int_val, .. }) => {
                let litint = syn::LitInt::new(lit_int_val, Span::call_site());
                syn::Expr::Lit(syn::ExprLit {
                    attrs: vec![],
                    lit: syn::Lit::Int(litint),
                })
            }
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
    }
}

fn to_pat_ident(p: &PatIdent) -> SynPat {
    SynPat::Ident(syn::PatIdent {
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
    })
}

fn to_syn_stmt(s: &Stmt) -> syn::Stmt {
    match s {
        Stmt::SLocal(s) => syn::Stmt::Local(Local {
            attrs: vec![],
            let_token: Let {
                span: Span::call_site(),
            },
            pat: {
                let Pat::PIdent(p) = &s.local_stmt_pat;
                to_pat_ident(&p)
            },
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
        Typ::TName(s) => {
            let path = to_syn_path(s.to_string());
            Type::Path(TypePath { qself: None, path })
        }
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
    }
}

fn to_syn_fn_arg(a: &FnArg) -> syn::FnArg {
    let FnArg::FnArgPat(pt) = a;
    let t = to_syn_typ(&pt.pat_typ_typ);
    let Pat::PIdent(p) = &pt.pat_typ_pat;
    let pat: SynPat = to_pat_ident(&p);
    syn::FnArg::Typed(PatType {
        attrs: vec![],
        pat: Box::new(pat),
        colon_token: Colon {
            spans: [Span::call_site()],
        },
        ty: Box::new(t),
    })
}

fn to_syn_fn_sig(s: &FnSig) -> Signature {
    let mut args: Punctuated<syn::FnArg, Comma> = Punctuated::new();
    s.fn_args.iter().for_each(|a| args.push(to_syn_fn_arg(a)));

    let mut generics: Punctuated<syn::GenericParam, Comma> = Punctuated::new();
    s.fn_generics.iter().for_each(|g| {
        let GenericParam::GenericTypeParam(g) = g;
        generics.push(syn::GenericParam::Type(syn::TypeParam {
            attrs: vec![],
            ident: Ident::new(g, Span::call_site()),
            colon_token: None,
            bounds: Punctuated::new(),
            eq_token: None,
            default: None,
        }))
    });

    Signature {
        constness: None,
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

fn fn_to_syn_string(f: &Fn) -> String {
    let f: ItemFn = to_syn_fn(f);
    quote::quote!(#f).to_string()
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match &self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
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
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Expr::EBinOp(e) => write!(f, "{} {} {}", e.expr_bin_left, e.op, e.expr_bin_right),
            Expr::EPath(s) => write!(f, "{}", s),
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
        }
    }
}

impl fmt::Display for Typ {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Typ::TName(s) => write!(f, "{}", s),
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
        }
    }
}

impl fmt::Display for LocalStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Pat::PIdent(p) = &self.local_stmt_pat;
        write!(
            f,
            "let {} {} {}",
            if p.is_mut { "mut" } else { "" },
            p.pat_name,
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
        let Pat::PIdent(p) = &pt.pat_typ_pat;
        // let FnArg::FnArgPat(Pat::PIdent(p)) = &self;
        write!(
            f,
            "{}:{} {} {}",
            p.pat_name,
            if p.by_ref { "&" } else { "" },
            if p.is_mut { "mut" } else { "" },
            pt.pat_typ_typ
        )
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

  fn rust_fn_to_syn_string(cr, e:OCamlRef<Fn>) -> OCaml<String> {
    let e = cr.get(e);
    let e: Fn = e.to_rust ();
    fn_to_syn_string(&e).to_owned ().to_ocaml(cr)
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
