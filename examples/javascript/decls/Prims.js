declare type list<a> = Cons<a> | Nil;
declare type Cons<a> = {_tag:"Cons", _0: a, _1: list<a>};
declare type Nil = {_tag:"Nil"};

declare type option<a> = Some<a> | None;
declare type Some<a> = {_tag:"Some", _0: a}; 
declare type None = {_tag:"None"};