# Independent model of the reduced grammar in CborBoundary.fst.
# Written from the RFC, not from the F* source, so the .expected values
# are not self-confirming.
def utf8_take(b, i, n):
    end = i + n
    if end > len(b): return None
    while i < end:
        c = b[i]
        if c <= 0x7F: i += 1
        elif 0xC2 <= c <= 0xDF:
            if i+2 > end or not (0x80 <= b[i+1] <= 0xBF): return None
            i += 2
        elif c in (0xE0,0xED) or 0xE1 <= c <= 0xEC or 0xEE <= c <= 0xEF:
            if i+3 > end: return None
            lo = 0xA0 if c == 0xE0 else 0x80
            hi = 0x9F if c == 0xED else 0xBF
            if not (lo <= b[i+1] <= hi) or not (0x80 <= b[i+2] <= 0xBF): return None
            i += 3
        elif 0xF0 <= c <= 0xF4:
            if i+4 > end: return None
            lo = 0x90 if c == 0xF0 else 0x80
            hi = 0x8F if c == 0xF4 else 0xBF
            if not (lo <= b[i+1] <= hi) or not (0x80 <= b[i+2] <= 0xBF) \
               or not (0x80 <= b[i+3] <= 0xBF): return None
            i += 4
        else: return None
    return end

M = (1 << 64) - 1
def minimal(ai, v):
    return {24: v >= 24, 25: v >= 256, 26: v >= 65536, 27: v >= 4294967296}.get(ai, True)

def item(fuel, b, i):
    if fuel == 0 or i >= len(b): return None
    b0 = b[i]; i += 1
    mt = b0 >> 5; ai = b0 & 0x1F
    if ai < 24: v = ai
    elif ai in (24,25,26,27):
        w = {24:1,25:2,26:4,27:8}[ai]
        if i + w > len(b): return None
        v = int.from_bytes(b[i:i+w], 'big'); i += w
    else: return None
    if not minimal(ai, v): return None
    if mt in (0,1): return i
    if mt == 2:
        return i + v if i + v <= len(b) else None
    if mt == 3:
        return utf8_take(b, i, v)
    if mt == 4:
        if v > len(b) - i: return None
        return items(fuel-1, v, b, i)
    if mt == 5:
        budget = len(b) - i
        if v > budget or v > budget - v: return None
        return items(fuel-1, (v*2) & M, b, i)
    if mt == 6: return item(fuel-1, b, i)
    if ai < 24: return i
    if ai == 24: return i if v >= 32 else None
    return None

def items(fuel, n, b, i):
    while True:
        if fuel == 0: return None
        if n == 0: return i
        r = item(fuel-1, b, i)
        if r is None: return None
        i = r; n -= 1; fuel -= 1

def validate(hexs):
    b = bytes.fromhex(hexs)
    r = item(64, b, 0)
    return r is not None and r == len(b)
