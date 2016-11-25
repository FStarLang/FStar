/* @flow */

export type buffer<T> = {
    _content: T[],
    _idx: number,
    _len: number
};

export let create = <T>(init:T): ((len:number) => buffer<T>) => ((len:number) => {
    let a = new Array(len);
    a.fill(init);
    return {
        _content: a,
        _idx: 0,
        _len: len
    };
});

export let createL = <T>(l:T[]): buffer<T> => {
    return {
        _content: l,
        _idx: 0,
        _len: l.length
    };
};

export let index = <T>(b:buffer<T>): ((n:number) => T) => ((n:number) => b._content[n + b._idx]);

export let upd = <T>(b:buffer<T>): ((n:number) => ((v:T) => null)) => ((n:number) => ((v:T) => {
    b._content[n + b._idx] = v;
    return null;
}));

export let sub = <T>(b:buffer<T>): ((i:number) => ((len:number) => buffer<T>)) => ((i:number) => ((len:number) => ({
        _content: b._content,
        _idx :  b._idx + i,
        _len: len 
})));

export let offset = <T>(b:buffer<T>): ((i:number) => buffer<T>) => ((i:number) => ({
        _content: b._content,
        _idx: b._idx + i,
        _len: b._len - i
}));

export let fill = <T>(b:buffer<T>): ((z:T) => ((len:number) => null)) => ((z:T) => ((len:number) => {
    b._content.fill(z, 0, len);
    return null;
}));

export let split = <T>(b:buffer<T>): ((i:number) => [buffer<T>, buffer<T>]) => ((i:number) => [sub(b)(0)(i), sub(b)(i)(b._len - i)]);

export let op_Array_Access = <T>(b:buffer<T>): ((n:number) => T) => ((n:number) => index(b)(n));

export let op_Array_Assignment = <T>(b:buffer<T>): ((n:number) => ((v:T) => null) ) => ((n:number) => ((v:T) => upd(b)(n)(v)));

export let blit = <T>(a:buffer<T>): ((idx_a: number) => ((b:buffer<T>) => ((idx_b:number) => ((len:number) => null)))) => ((idx_a: number) => ((b:buffer<T>) => ((idx_b:number) => ((len:number) => {
    for (let i = 0; i < len; i++){
        b._content[b._idx + idx_b + i] = a._content[a._idx + idx_a + i];
    };
    return null;
}))));