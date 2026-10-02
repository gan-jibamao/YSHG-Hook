#!/usr/bin/env python3
# protect.py — 常量段加密 (源码 deobf() 契约的构建侧)
# 用法: python3 protect.py <dylib>
#   · 解析 Mach-O, 定位 __DATA,__cstr (整段 ChaCha20 加密, ctr0 = i * 0x9E3779B9)
#   · 明文段 CRC32 (zlib) 写入 g_ck.r[i].crc — deobf() 解密后按 CRC 校验
#   · g_ck (魔数 9E 37 C4 51 AB 0F 62 D8, 位于 __DATA,__data) 填 nranges/ranges,
#     key/nonce 按 CKMASK(i) = kCkSig[i%8] ^ (i*0x5D+0x3C) 掩码落盘
#   · 加密后须重签: ldid -S
import struct, sys, zlib, secrets

CKSIG = bytes([0x9E, 0x37, 0xC4, 0x51, 0xAB, 0x0F, 0x62, 0xD8])
CKMASK = lambda i: CKSIG[i % 8] ^ ((i * 0x5D + 0x3C) & 0xFF)
BLOB_SZ = 8 + 4 + 4 + 4 * 24 + 32 + 12          # magic,nranges,flags,r[4],key[32],nonce[12]
GCK_BLOB_OFF = 16                                # r[0] 在 blob 内偏移; key 112; nonce 144

def rotl32(v, c): return ((v << c) | (v >> (32 - c))) & 0xFFFFFFFF

def cc20_block(key, nonce, ctr):
    st = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574]
    st += [int.from_bytes(key[i*4:i*4+4], 'little') for i in range(8)]
    st.append(ctr & 0xFFFFFFFF)
    st += [int.from_bytes(nonce[i*4:i*4+4], 'little') for i in range(3)]
    w = st[:]
    for _ in range(10):
        for a, b, c, d in [(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),
                           (0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]:
            w[a] = (w[a] + w[b]) & 0xFFFFFFFF; w[d] = rotl32(w[d] ^ w[a], 16)
            w[c] = (w[c] + w[d]) & 0xFFFFFFFF; w[b] = rotl32(w[b] ^ w[c], 12)
            w[a] = (w[a] + w[b]) & 0xFFFFFFFF; w[d] = rotl32(w[d] ^ w[a], 8)
            w[c] = (w[c] + w[d]) & 0xFFFFFFFF; w[b] = rotl32(w[b] ^ w[c], 7)
    return b''.join(((w[i] + st[i]) & 0xFFFFFFFF).to_bytes(4, 'little') for i in range(16))

def cc20_xor(buf, key, nonce, ctr0):
    out = bytearray(); ctr = ctr0 & 0xFFFFFFFF
    for i in range(0, len(buf), 64):
        ks = cc20_block(key, nonce, ctr); ctr = (ctr + 1) & 0xFFFFFFFF
        chunk = buf[i:i+64]
        out += bytes(a ^ b for a, b in zip(chunk, ks))
    return bytes(out)

def parse(data):
    ncmds = struct.unpack_from('<I', data, 16)[0]
    off, secs = 32, {}
    for _ in range(ncmds):
        cmd, cmdsize = struct.unpack_from('<II', data, off)
        if cmd == 0x19:                                   # LC_SEGMENT_64
            segname = data[off+8:off+24].rstrip(b'\0').decode()
            nsects = struct.unpack_from('<I', data, off+64)[0]
            so = off + 72
            for _ in range(nsects):
                sect = data[so:so+16].rstrip(b'\0').decode()
                addr, size = struct.unpack_from('<QQ', data, so+32)
                fo = struct.unpack_from('<I', data, so+48)[0]
                secs[(sect, segname)] = (addr, size, fo)
                so += 80
        off += cmdsize
    return secs

def find_gck(data, secs):
    addr, size, fo = secs[('__data', '__DATA')]
    pat = CKSIG + b'\0' * 4 + b'\0' * 4 + b'\0' * 96      # magic + nranges=0 + flags=0 + r[4]全零
    idx = data.find(pat, fo, fo + size)
    return idx if idx >= 0 else None

def main():
    path = sys.argv[1]
    data = bytearray(open(path, 'rb').read())
    assert struct.unpack_from('<I', data, 0)[0] == 0xFEEDFACF, 'not arm64 Mach-O'
    secs = parse(data)
    assert ('__cstr', '__DATA') in secs, '__DATA,__cstr 缺失 (链接时未 -rename_section?)'
    gck = find_gck(data, secs)
    assert gck is not None, 'g_ck 未定位 (魔数哨兵不在 __DATA,__data)'

    key, nonce = secrets.token_bytes(32), secrets.token_bytes(12)
    targets = [s for s in [('__cstr', '__DATA'), ('__tconst', '__DATA')] if s in secs]
    ranges = []
    for i, s in enumerate(targets):
        addr, size, fo = secs[s]
        pt = bytes(data[fo:fo+size])
        crc = zlib.crc32(pt) & 0xFFFFFFFF
        data[fo:fo+size] = cc20_xor(pt, key, nonce, i * 0x9E3779B9)
        ranges.append((addr, size, crc))
        print(f'  加密 {s[0]}: addr=0x{addr:x} size=0x{size:x} crc=0x{crc:08x} ctr0=0x{i*0x9E3779B9:x}')

    o = gck
    data[o+8:o+12] = struct.pack('<I', len(ranges))       # nranges (flags 保持 0)
    pos = o + GCK_BLOB_OFF
    for addr, size, crc in ranges:
        struct.pack_into('<QQII', data, pos, addr, size, crc, 5)   # prot=RX (deobf 不读)
        pos += 24
    for j in range(32): data[o+112+j] = key[j] ^ CKMASK(j)
    for j in range(12): data[o+144+j] = nonce[j] ^ CKMASK(j)
    open(path, 'wb').write(data)

    # ---- 验证: 模拟 deobf() 走一遍, 明文必须逐字节还原 ----
    data2 = open(path, 'rb').read()
    nr = struct.unpack_from('<I', data2, gck+8)[0]
    r0 = struct.unpack_from('<QQII', data2, gck+16)
    k2 = bytes(data2[gck+112+j] ^ CKMASK(j) for j in range(32))
    n2 = bytes(data2[gck+144+j] ^ CKMASK(j) for j in range(12))
    addr, size, crc, prot = r0
    fo = secs[('__cstr', '__DATA')][2]
    pt2 = cc20_xor(data2[fo:fo+size], k2, n2, 0)
    ok = zlib.crc32(pt2) & 0xFFFFFFFF == crc
    print(f'  验证: nranges={nr} 魔数ok={data2[gck:gck+8]==CKSIG} 解密CRC={"PASS" if ok else "FAIL"}')
    if not ok: sys.exit('CRC 校验失败, 文件已保留密文态 — 回滚重跑')

if __name__ == '__main__':
    main()