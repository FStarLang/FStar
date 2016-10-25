declare type list<a> = Cons<a> | Nil;
declare type Cons<a> = {_tag:"Cons", _0: [a, list<a>]};
declare type Nil = {_tag:"Nil", _0: []};

declare type option<a> = Some<a> | None;
declare type Some<a> = {_tag:"Some", _0: [a]}; 
declare type None = {_tag:"None", _0: []};