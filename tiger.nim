# Tiger Hash function based on the reference
# implementation by Ross Anderson and Eli Biham.

# Copywrite 2017 Emery Hemingway
# MIT licensed

{.overflowChecks: off.}
# Integers will overflow.

const
  BlockSize* = 64

type
  Word = int64
  Block* = array[BlockSize, char]
  TigerDigest* = array[3, int64]

  TigerState* = object
    data: Block
    registers: TigerDigest
    total: int
    off: int

include sboxes
template t1(x: Word): Word = table1[x and 0xFF]
template t2(x: Word): Word = table2[x and 0xFF]
template t3(x: Word): Word = table3[x and 0xFF]
template t4(x: Word): Word = table4[x and 0xFF]

template round(a, b, c, x: var Word, mul: Word) =
  c = c xor x
  a = a - (
    t1(c shr (0*8)) xor
    t2(c shr (2*8)) xor
    t3(c shr (4*8)) xor
    t4(c shr (6*8)))
  b = b + (
    t4(c shr (1*8)) xor
    t3(c shr (3*8)) xor
    t2(c shr (5*8)) xor
    t1(c shr (7*8)))
  b = b * mul

template pass(a, b, c, x0, x1, x2, x3, x4, x5, x6, x7: var Word, mul: Word) =
  round(a,b,c,x0,mul)
  round(b,c,a,x1,mul)
  round(c,a,b,x2,mul)
  round(a,b,c,x3,mul)
  round(b,c,a,x4,mul)
  round(c,a,b,x5,mul)
  round(a,b,c,x6,mul)
  round(b,c,a,x7,mul)

template keySchedule(x0, x1, x2, x3, x4, x5, x6, x7: var Word) =
  x0 = x0 - (x7 xor 0xA5A5A5A5A5A5A5A5)
  x1 = x1 xor x0
  x2 = x2 + x1
  x3 = x3 - (x2 xor ((not x1) shl 19))
  x4 = x4 xor x3
  x5 = x5 + x4
  x6 = x6 - (x5 xor ((not x4) shr 23))
  x7 = x7 xor x6
  x0 = x0 + x7
  x1 = x1 - (x0 xor ((not x7) shl 19))
  x2 = x2 xor x1
  x3 = x3 + x2
  x4 = x4 - (x3 xor ((not x2) shr 23))
  x5 = x5 xor x4
  x6 = x6 + x5
  x7 = x7 - (x6 xor 0x0123456789ABCDEF)

proc tigerCompress(data: ptr Block, state: var TigerDigest) =
  let data = cast[ptr array[8, Word]](data)
  var
    a {.register.} = state[0]
    b {.register.} = state[1]
    c {.register.} = state[2]

    x0=data[0]
    x1=data[1]
    x2=data[2]
    x3=data[3]
    x4=data[4]
    x5=data[5]
    x6=data[6]
    x7=data[7]

  let
    aa = a
    bb = b
    cc = c

  pass(a, b, c, x0, x1, x2, x3, x4, x5, x6, x7, 5)
  keySchedule(x0, x1, x2, x3, x4, x5, x6, x7)
  pass(c, a, b, x0, x1, x2, x3, x4, x5, x6, x7, 7)
  keySchedule(x0, x1, x2, x3, x4, x5, x6, x7)
  pass(b, c, a, x0, x1, x2, x3, x4, x5, x6, x7, 9)

  state[0] = a xor aa
  state[1] = b - bb
  state[2] = c + cc

proc init*(result: var TigerState) =
  result.registers = [
    0x0123456789ABCDEF, 0xFEDCBA9876543210, 0xF096A5B4C3B2E187 ]
  result.total = 0

proc reset*(result: var TigerState) =
  for i in result.data.low .. result.data.high:
    result.data[i] = 0.char
  init result

proc process*(state: var TigerState, buffer: var openArray[char]) =
  let total = buffer.len
  if total != 0:
    let
      blockOff = (BlockSize + state.total) mod BlockSize
      blockFill = min(blockOff, total)
    if blockOff != 0:
      copyMem(addr state.data[blockOff], addr buffer, blockFill)
      if blockFill < total:
        tigerCompress(addr state.data, state.registers)

    var count = blockFill
    while (total - count) >= BlockSize:
      tigerCompress(cast[ptr Block](addr buffer[count]), state.registers)
      inc(count, BlockSize)

    if count < total:
      copyMem(addr state.data, addr buffer[count], total - count)

    inc(state.total, total)

proc digest*(state: var TigerState): TigerDigest =
  var temp: Block
  var j = (BlockSize + state.total) mod BlockSize
  copyMem(addr temp, addr state.data, j)

  when system.cpuEndian == bigEndian:
    raise newException(SystemError, "big endian support not implemented")

  temp[j] = 0x01.char
  inc j
  while (j and 7) != 0:
    inc j
  if j > 56:
    while j < 64:
      temp[j] = 0.char
      inc j
    tigerCompress(addr temp, state.registers)
    j = 0
  while j < 56:
    temp[j] = 0.char
    inc j

  var total = state.total shl 3
  copyMem(addr temp[56], addr total, 8)
  tigerCompress(addr temp, state.registers)
  result = state.registers

proc tiger*(data: string): TigerDigest =
  var
    state: TigerState
    data = data
  init state
  state.process(data)
  state.digest()

when isMainModule:
  import strutils, times, unittest

  proc `$`(d: TigerDigest): string =
    result =
      toHex(d[0] shr 32, 8) & toHex(d[0], 8) & " " &
      toHex(d[1] shr 32, 8) & toHex(d[1], 8) & " " &
      toHex(d[2] shr 32, 8) & toHex(d[2], 8)

  template test(data: string, control: string) =
    echo "\"", data, "\""
    let res = $tiger(data)
    test res:
      check(res == control)

  suite "Hash of short strings":

    test("", "24F0130C63AC9332 16166E76B1BB925F F373DE2D49584E7A")

    test("abc", "F258C1E88414AB2A 527AB541FFC5B8BF 935F7B951C132951")

    test("Tiger", "9F00F599072300DD 276ABB38C8EB6DEC 37790C116F9D2BDF")

  suite "Hash of 512-bit strings":

    test("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-", "87FB2A9083851CF7 470D2CF810E6DF9E B586445034A5A386")

    test("ABCDEFGHIJKLMNOPQRSTUVWXYZ=abcdefghijklmnopqrstuvwxyz+0123456789", "467DB80863EBCE48 8DF1CD1261655DE9 57896565975F9197")

    test("Tiger - A Fast New Hash Function, by Ross Anderson and Eli Biham", "0C410A042968868A 1671DA5A3FD29A72 5EC1E457D3CDB303")

  suite "Hash of two-block strings strings":

    test("Tiger - A Fast New Hash Function, by Ross Anderson and Eli Biham, proceedings of Fast Software Encryption 3, Cambridge.", "EBF591D5AFA655CE 7F22894FF87F54AC 89C811B6B0DA3193")

    test("Tiger - A Fast New Hash Function, by Ross Anderson and Eli Biham, proceedings of Fast Software Encryption 3, Cambridge, 1996.", "3D9AEB03D1BD1A63 57B2774DFD6D5B24 DD68151D503974FC")

    test("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-", "00B83EB4E53440C5 76AC6AAEE0A74858 25FD15E70A59FFE4")

  suite "Hash of a 64K-byte string":
    var big = newString 65536
    for i in big.low .. big.high:
      big[i] = (i and 0xFF).char
    const control = "8EF43951B3F5F4FD 1D41AFE51B420E71 0462F233C3AAA8E1"
    let res = $tiger(big)
    test res:
      check(res == control)
