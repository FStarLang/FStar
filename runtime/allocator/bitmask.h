#ifndef __BITMASK_H__
#define __BITMASK_H__

void setbit(unsigned char *map, int bit);
void unsetbit(unsigned char *map, int bit);
void unsetbit_rng(unsigned char *map, int bit, int len);

typedef void (*bitfun)(void *env, int index);
void eachbit(unsigned char *map, int maxbit, bitfun f, void *env);

#endif
