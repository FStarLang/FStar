(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
﻿#light "off"

module FStar.Backends.JS.Print

open FStar.Backends.JS.Ast
open System
open System.Text
open FSharp.Format

let semi = text ";"
let comma = text ","
let dot = text "."
let colon = text ":"
let lbr = text "["
let rbr = text "]"
let ws = break1

let encode_char (c : char) =
  let cn = (int)c in
  if cn > 127 || cn=39 then sprintf "\\u%04x" cn
  else match cn with
    | 34 -> "\\\"" | 92 -> "\\\\"
    | 9 -> "\\t"   | 10 -> "\\n"
    | 11 -> "\\v"  | 12 -> "\\f"
    | 8 -> "\\b"   | 47 -> "\\/"  | 13 -> "\\r"
    | n -> if n < 32 then sprintf "\\x%02x" cn else sprintf "%c" c

let jstr_escape s = String.collect encode_char s

let rec pretty_print (program:Ast.t) : doc =
  program
  |> List.map (function
    | JS_Statement(s) -> pretty_print_statement s
    | JS_FunctionDeclaration(f) -> pretty_print_function f)
  |> reduce (* combine hardline *)

and pretty_print_statement (p:statement_t) : doc =
  let optws (s:statement_t) = match s with JSS_Block(_) -> pretty_print_statement s
    | _ -> reduce [ws; nest 1 (pretty_print_statement s)] in
  let f = function
  | JSS_Empty -> semi
  | JSS_Debugger -> reduce [ws; text "debugger;"]

  | JSS_Return(e) -> reduce [ws; text "return";
    (match e with None -> empty
    | Some v -> reduce [ws; pretty_print_exp v]);
    semi]

  | JSS_Throw(e) -> reduce [ws; text "throw "; pretty_print_exp e; semi]

  | JSS_Break(i) -> reduce [ws; text "break";
    (match i with None -> empty | Some v -> cat ws (text v));
    semi]

  | JSS_Continue(i) -> reduce [ws; text "continue";
    (match i with None -> empty | Some v -> reduce [ws; text (jstr_escape v)]);
    semi]

  | JSS_Block(l) -> reduce [ws; text "{"; hardline; nest 1 (pretty_print_statements l); ws; text "}"]

  | JSS_Label(l, s) -> reduce [ws; text (jstr_escape l); text ":"; hardline; optws s]

  | JSS_Expression(e) -> reduce [ws; (pretty_print_exp e); semi]

  | JSS_If(c,t,f) -> reduce [ws; text "if"; (parens (pretty_print_exp c)); hardline; optws t;
    (match f with None -> empty | Some s -> reduce [ws; text "else";
      (match s with JSS_If(_) -> ws | _ -> hardline); optws s])]

  | JSS_Do(s,e) -> reduce [ws; text "do"; hardline; optws s; pretty_print_statement s;
    ws; text "while"; parens (pretty_print_exp e); semi]

  | JSS_While(e,s) -> reduce [ws; text "while"; parens (pretty_print_exp e); hardline; optws s]

  | JSS_For(i,c,l,s) -> reduce [ws; text "for"; reduce [
    (match i with None -> empty
     | Some e -> (match e with JSF_Expression(f) -> pretty_print_exp_il f
        | JSF_Declaration(l) -> List.map
            (fun (x,vl) -> reduce [text "var"; ws; text (jstr_escape x);
                (match vl with None -> empty | Some v -> reduce [ws; text "="; ws; pretty_print_exp_cl v])]
            ) l |> combine comma)
    ); semi; ws;
    (match c with None -> empty | Some e -> pretty_print_exp e); semi; ws;
    (match l with None -> empty | Some e -> pretty_print_exp e)] |> parens;
    hardline; optws s]

  | JSS_Forin(i,e,s) -> reduce [ws; text "for"; reduce [
    (match i with JSF_Expression(f) -> pretty_print_exp_il f
    | JSF_Declaration(l) -> List.map (fun (x,v) -> reduce [text "var"; ws; text (jstr_escape x);
        (match v with None->empty | Some v -> reduce [ws; text "="; ws; pretty_print_exp_cl v])])
    l |> combine comma); ws; colon; ws; pretty_print_exp e] |> parens;
    hardline; optws s]

  | JSS_With(e,s) -> reduce [ws; text "with"; parens (pretty_print_exp e); hardline; optws s]

  | JSS_Switch(e,def,cases) -> reduce [ws; text "switch"; parens (pretty_print_exp e); hardline;
      ws; text "{"; hardline; reduce [
        combine hardline (List.map (fun (e,l)->reduce [ws; text "case "; pretty_print_exp e; colon; hardline; nest 1 (pretty_print_statements l)]) cases);
        (match def with None -> empty | Some l -> reduce [ws; text "default:"; hardline; nest 1 (pretty_print_statements l)])
      ] |> nest 1; ws; text "}"]

  | JSS_Try(b,c,f) -> reduce [ws; text "try"; hardline; (pretty_print_statement b);
      (match c with Some (i,c) -> reduce [ws; text "catch"; parens (text i); hardline; (pretty_print_statement c)]| None -> empty);
      (match f with Some f -> reduce [ws; text "finally"; hardline; (pretty_print_statement f)] | None -> empty)]

  | JSS_Declaration(l) -> reduce [ws; text "var"; ws; combine comma (List.map
      (fun (i,v) -> reduce [text (jstr_escape i);
        (match v with None -> empty
        | Some v -> reduce [ws; text "="; ws; pretty_print_exp_cl v])]) l); semi]

  in reduce [(f p) ; hardline]

and pretty_print_statements l = reduce (List.map pretty_print_statement l)

and pt s b = if b then parens s else s

and pretty_print_exp_gen (commaless:bool) (inless:bool) =
  let rec ppe input = match input with
  | JSE_This -> (text "this", 0)
  | JSE_Null -> (text "null", 0)
  | JSE_Undefined -> (text "undefined", 0)
  | JSE_Elision -> (text "undefined", 0)
  | JSE_Bool(b) -> (text (if b then "true" else "false"), 0)
  | JSE_Number(n) -> (text (sprintf "%F" n), 0)
  | JSE_String(s) -> (text (sprintf "\"%s\"" (jstr_escape s)), 0)
  | JSE_Regexp(r,f) -> (text (sprintf "/%s/%s" (jstr_escape r) f), 0)
  | JSE_Identifier(id) -> (text (jstr_escape id), 0)
  | JSE_Array(l) -> (enclose lbr rbr (pretty_print_elist l), 0)
  | JSE_Object(l) -> ((if List.length l > 0 then reduce [
    text "{"; hardline; (pretty_print_object l); ws; text "}"] else text "{}"), 0)
  | JSE_Function(f) -> (parens (pretty_print_function f), 1)
  | JSE_Dot(e,i) -> let (s,p)=ppe e in (reduce [pt s (p>1); text "."; text (jstr_escape i)], 1)
  | JSE_Property(e,f) -> let (s,p) = ppe e in let (s1, p1) = ppe f in (reduce [pt s (p>1); enclose lbr rbr s1],1)
  | JSE_Call(f, l) -> let (s,p) = ppe f in (reduce [pt s (p>1); text "("; (pretty_print_elist l); text ")"],1)
  | JSE_New(e, f) -> let (s,p)=ppe e in (reduce [text "new "; pt s (p>2);
      (match f with Some l->parens (pretty_print_elist l) | None -> empty)], 2)
  | JSE_Preincr(e) -> una e "++"
  | JSE_Predecr(e) -> una e "--"
  | JSE_Postincr(e) -> let (s,p)=ppe e in (reduce [pt s (p>3); text "++"], 3)
  | JSE_Postdecr(e) -> let (s,p)=ppe e in (reduce [pt s (p>3); text "--"], 3)
  | JSE_Plus(e) -> una e "+"
  | JSE_Minus(e) -> una e "-"
  | JSE_Bnot(e) -> una e "~"
  | JSE_Lnot(e) -> una e "!"
  | JSE_Typeof(e) -> una e "typeof"
  | JSE_Delete(e) -> una e "delete"
  | JSE_Void(e) -> una e "void"
  | JSE_Mod(e,f) -> bin e f 6 3 "%" 4
  | JSE_Divide(e,f) -> bin e f 6 4 "/" 5
  | JSE_Multiply(e,f) -> bin e f 6 6 "*" 6
  | JSE_Add(e,f) -> bin e f 7 7 "+" 7
  | JSE_Sub(e,f) -> bin e f 7 7 "-" 7
  | JSE_Lsh(e,f) -> bin e f 8 7 "<<" 8
  | JSE_Rsh(e,f) -> bin e f 8 7 ">>" 8
  | JSE_Ash(e,f) -> bin e f 8 7 ">>>" 8
  | JSE_Lt(e,f) -> bin e f 9 8 "<" 9
  | JSE_Le(e,f) -> bin e f 9 8 "<=" 9
  | JSE_Ge(e,f) -> bin e f 9 8 ">=" 9
  | JSE_Gt(e,f) -> bin e f 9 8 ">" 9
  | JSE_In(e,f) -> bin e f 9 8 "in" 9
  | JSE_Instanceof(e,f) -> bin e f 9 8 "instanceof" 9
  | JSE_Equal(e,f) -> bin e f 10 9 "==" 10
  | JSE_Sequal(e,f) -> bin e f 10 9 "===" 10
  | JSE_Band(e,f) -> bin e f 11 10 "&" 11
  | JSE_Bxor(e,f) -> bin e f 12 11 "^" 12
  | JSE_Bor(e,f) -> bin e f 13 12 "|" 13
  | JSE_Land(e,f) -> bin e f 14 13 "&&" 14
  | JSE_Lor(e,f) -> bin e f 15 14 "||" 15
  | JSE_Conditional(c,e,f) -> let (s1,p1)=ppe c in let (s2,p2)=ppe e in let (s3,p3)=ppe f in
    (reduce [pt s1 (p1>16); text " ? "; pt s2 (p2>16); text " : " ; pt s3 (p3>16)], 16)
  | JSE_Assign(e,f) -> bin e f 16 17 "=" 17
  | JSE_Ashassign(e,f) -> bin e f 16 17 ">>>=" 17
  | JSE_Sequence(e) -> (pt (pretty_print_elist e) commaless, 18)
  and una e op = let (s,p)=ppe e in (reduce [text op; pt s (p>3)], 3)
  and bin e f k1 k2 op pr = let (s1,p1)=ppe e in let (s2,p2)=ppe f in
    (reduce [pt s1 (p1>k1); ws; text op; ws; pt s2 (p2>k2)], pr)
  in fun e -> fst (ppe e)

and pretty_print_exp : expression_t -> doc = pretty_print_exp_gen false false
and pretty_print_exp_cl = pretty_print_exp_gen true false
and pretty_print_exp_il = pretty_print_exp_gen false true

and pretty_print_elist l = List.map pretty_print_exp_cl l |> combine comma

and pretty_print_function_decl (decl:bool) ((n,args,b):function_t) = reduce [
  (if decl then reduce [text "function"; ws; text (match n with Some(i) -> jstr_escape i | None -> "")] else empty);
  parens (pretty_print_elist (List.map (fun s->JSE_Identifier(s)) args));
  (match List.length b with 0 -> text "{}"
  | _ -> reduce [hardline; ws; text "{"; hardline; ws; nest 1 (pretty_print b); ws; text "}"])]

and pretty_print_function = pretty_print_function_decl true

and pretty_print_object = function
  | h::t -> let p = match h with
    | JSP_Property(p, v) -> reduce [ws; text "\""; text (jstr_escape p); text "\":"; (pretty_print_exp_cl v)]
    | JSP_Getter(p,f) -> cat (text ("get "^(jstr_escape p))) (pretty_print_function_decl false f)
    | JSP_Setter(p,f) -> cat (text ("set "^(jstr_escape p))) (pretty_print_function_decl false f)
    in reduce [p; (if List.length t>0 then comma else empty); hardline; pretty_print_object t]
  | [] -> empty


