declare type list<a> = Cons<a> | Nil;
declare type Cons<a> = {_tag:"Cons", _value: [a, list<a>]};
declare type Nil = {_tag:"Nil", _value: []};

declare type option<a> = Some<a> | None;
declare type Some<a> = {_tag:"Some", _value: [a]}; 
declare type None = {_tag:"None", _value: []};