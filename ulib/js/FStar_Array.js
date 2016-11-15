/* @flow */

export type array<T> = T[];

export let create = <T>(n:number): ((init:T) => T[]) => ((init:T) => {
    let a = new Array(n);
    a.fill(init);
    return a;
}); 

export let length = <T>(x:T[]): number => x.length;

export let index = <T>(x:T[]): ((n:number) => T) => ((n:number) => x[n]);

export let swap = <T>(x:T[]): ((i:number) => ((j:number) => T[])) => ((i:number) => ((j:number) => {
    let tmp = x[i];
    x[i] = x[j];
    x[j] = tmp;
    return x;
}));

export let append = <T>(a1:T[]): ((a2:T[]) => T[]) => ((a2:T[]) => a1.concat(a2));

export let eq = <T>(a1:T[]): ((a2:T[]) => boolean) => ((a2:T[]) => a1.length == a2.length && a1.every((v,i) => v === a2[i]));

export let split = <T>(a:T[]): ((i:number) => [T[], T[]]) => ((i:number) => [a.slice(0, i), a.slice(i)]);