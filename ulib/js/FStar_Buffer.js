/* @flow */

export type buffer = Uint32Array; 

export let create =  (init:number) : ((len:number) => buffer) => ((len:number) => {
    let res = new Uint32Array(len);
    res.fill(init);
    return res;
});
 
export let createL = (l:Array<number>): buffer => Uint32Array.from(l);    
    
export let index = (b:buffer) => ((n:number) => b[n]);

export let upd = (b:buffer) => ((n:number) => ((v:number) => {
    b[n] = v;
    return null;
}));

export let sub = (b:buffer) => ((i:number) => ((len:number) => b.subarray(i, i + len)));

export let offset = (b:buffer) => ((i:number) => b.subarray(i, b.length));

export let blit = (a:buffer) => ((idx_a:number) => ((b:buffer) => ((idx_b:number) => ((len:number) => {
    let tmp = sub(a)(idx_a)(len);
    b.set(tmp, idx_b);
    return b;
})))); 

export let fill = (b:buffer) => ((z:number) => ((len:number) => b.fill(z, 0, len)));

export let split = (b:buffer) => ((i:number) =>  [sub(b)(0)(i), sub(b)(i)(b.length - i)]);

export let op_Array_Access = (b:buffer) => ((n:number) => index(b)(n));

export let op_Array_Assignment = (b:buffer) => ((n:number) => ((v:number) => upd(b)(n)(v)));