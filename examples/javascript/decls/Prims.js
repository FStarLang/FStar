declare type list<T> = Cons<T> | Nil;
declare type Cons<T> = {_tag:"Cons", _0: a, _1: list<T>};
declare type Nil = {_tag:"Nil"};

declare type option<T> = Some<T> | None;
declare type Some<T> = {_tag:"Some", _0: T}; 
declare type None = {_tag:"None"};

export var _is_None = <T>(x:option<T>):boolean => {
    if (x._tag === "None"){
        return true;
    } else {
        return false;
    }
};

export var _is_Some = <T>(x:option<T>):boolean => {
    if (x._tag === "Some"){
        return true;
    } else {
        return false;
    }
};

export var _get_Some_0 = <T>(x:option<T>):T => {
    if (x._tag === "Some"){                
        return x._0;
    } else {
        throw "This value doesn't match! ";
    }
};

export var _mk_Some = <T>(v:T): option<T> => ({
    _tag: "Some",
    _0: v
});

export var _mk_None = <T>(): option<T> => ({
    _tag: "None"
});

export var _is_Cons = <T>(x:list<T>):boolean =>{
    if (x._tag === "Cons"){
        return true;
    } else{
        return false;
    }
};

export var _is_Nil = <T>(x:list<T>):boolean =>{
    if (x._tag === "Nil"){
        return true;
    } else{
        return false;
    }
};

export var _get_Cons_0 = <T>(x:list<T>): T =>{
    if (x._tag === "Cons"){
        return x._0;
    } else{
        throw "This value doesn't match! ";
    }
};

export var _get_Cons_1 = <T>(x:list<T>): list<T> =>{
    if (x._tag === "Cons"){
        return x._1;
    } else{
        throw "This value doesn't match! ";
    }
};

export var _mk_Cons = <T>(hd:T): ((tl:list<T>) => list<T>) => ((tl:list<T>) => ({
    _tag: "Cons",
    _0 : hd,
    _1: tl
}));

export var _mk_Nil = <T>():list<T> => ({
    _tag: "Nil"
});