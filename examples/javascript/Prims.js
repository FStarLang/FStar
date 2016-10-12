export type list<a> = Cons<a>|Nil;
type Cons<a> = {_tag:"Cons", _value: [a, List<a>]};
type Nil = {_tag:"Nil", _value: []};

export type option<a> = Some<a>|None;
type Some<a> = {_tag:"Some", _value: [a]}; 
type None = {_tag:"None", _value: []};