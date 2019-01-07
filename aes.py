#!/usr/bin/python
# Copyright 2004, 2019, Clemens Fruhwirth <clemens@endorphin.org>

# My pedagocial Rijndael implementation in Python.

# DO NOT USE IN PRODUCTION OR WITH ANY PRODUCTION SECRETS THIS IS MY
# TOY IMPLEMENTATION OF AES, WHICH I WROTE IN 2004 TO LEARN PYTHON AND
# AES.

from tmath import *
from marshal import *
import copy

# These are the basic fields we're using in Rijndael

Z2 = Z(2)                            # Residue class 2 field
POFZ2 = POF(Z2)                      # Polynomial over field Z2
rps = L2POL([1, 1, 0, 1, 1, 0, 0, 0, 1], Z2)  # Reduction polynomial in POFZ2
GFPOFZ2 = GFPOF(Z2, rps)              # Galious field over Z2 with reduction polynomial

def debug(msg, state):
  print msg,
  dumpStateHex(state)
  print ""

def rol(val, shift, length):
  if val > (1 << length):
    raise Error
  return ((val << shift) & ((1 << length)-1)) | (val >> (length-shift))

def XORsum(a, length):
  r = 0
  while not a == 0:
    r = r ^ (a&1)
    a = a >> 1
  return r

def fGen(a, mask, final):
  res = []
  for i in range(0, 8):
    res.append(XORsum(a & mask, 8))
    mask = rol(mask, 1, 8)
  return fromBin(res) ^ final

def f(a):
  return fGen(a, 0xF1, 0x63)

def fInv(a):
  return fGen(a, 0xA4, 0x05)

def g(a):
  if a == 0: return 0
  return fromBin(POL2L(EL2POL(L2EL(toBin(a), Z2), GFPOFZ2).mulInv()))

def SR(a):
  return STable[a]

def SRInv(a):
  return SInvTable[a]

STable = []
SInvTable = []
for i in range(0, 0x100):
  STable.append(f(g(i)))
  SInvTable.append(g(fInv(i)))

RCCache = [0x00, 0x01]

def RC(a):
  if a >= len(RCCache):
    newval = xtime(RC(a-1))
    RCCache.append(newval)
  return RCCache[a]

def xtime(a):
  pol = EL2POL(L2EL(toBin(a), Z2), GFPOFZ2)
  newpol = GFPOFZ2.xtime(pol)
  return fromBin(EL2L(POL2EL(newpol)))

def keyExpansion(cipherKey, nr, nk, nb):
  expandedKey = []
  for j in range(0, nk):
    expandedKey.append(cipherKey[j])
  for j in range(nk,  nb*(nr+1)):
    if j%nk == 0:
      sub = []
      sub.append(expandedKey[j-nk][0] ^ SR(expandedKey[j-1][1]) ^ RC(j/nk))
      for i in range(1, 4):
        sub.append(expandedKey[j-nk][i] ^ SR(expandedKey[j-1][(i+1)%4]))
      expandedKey.append(sub)
    else:
      sub = []
      for i in range(0, 4):
        sub.append(expandedKey[j-nk][i] ^ expandedKey[j-1][i])
      expandedKey.append(sub)
  return expandedKey

def SubBytes(state, function):
  r = []
  for i in state:
    r.append(map(function, i))
  return r

ShiftRowsOffsets = [[0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4]]

def ShiftRows(state, amp):
  offsets = ShiftRowsOffsets[len(state)-4]
  newstate = copy.deepcopy(state)
  r = []
  for j in range(0, len(state)):
    s = []
    for i in range(0, 4):
      newstate[j][i] = state[(j+offsets[i]*amp)%len(state)][i]
  return newstate

def RORRay(array, amount):
  new = []
  for i in array[-amount:]:
    new.append(i)
  for i in array[0:-amount]:
    new.append(i)
  return new

def SingleMixColumn(stateSub, coeffs):
  resStateSub = []
  localcoeffs = RORRay(coeffs, 0)
  for j in range(0, 4):
    res = GFPOFZ2.plusID()
#    print "LC: ", localcoeffs
    for i in range(0, 4):
      pol1 = EL2POL(L2EL(toBin(stateSub[i]), Z2), GFPOFZ2)
      pol2 = EL2POL(L2EL(toBin(localcoeffs[i]), Z2), GFPOFZ2)
      mulres = GFPOFZ2.mul(pol1, pol2)
#      print "pol1:",  pol1,  "pol2:", pol2,  "mulres: ", mulres
      res = GFPOFZ2.plus(res, mulres)
    fb = fromBin(EL2L(POL2EL(res)))
    resStateSub.append(fb)
    localcoeffs = RORRay(localcoeffs, 1)
  return resStateSub

def MixColumns(state, coeffs):
  return map(lambda x: SingleMixColumn(x, coeffs), state)

def AddRoundKey(state, subkey):
  return map(lambda stateSL, keySL: map(lambda stateE, keyE: stateE^keyE, stateSL, keySL),  state, subkey)

def round(state, subkey, round):
  state = SubBytes(state, SR)
  debug("R[%d].s_box" % round, state)
  state = ShiftRows(state, 1)
  debug("R[%d].s_row" % round, state)
  state = MixColumns(state, [0x02, 0x03, 0x01, 0x01])
  debug("R[%d].m_col" % round, state)
  state = AddRoundKey(state, subkey)
  debug("R[%d].k_sch" % round, subkey)
  return state

def invRound(state, subkey, round):
  state = AddRoundKey(state, subkey)
  state = MixColumns(state, [0x0E, 0x0B, 0x0D, 0x09])
  state = ShiftRows(state, -1)
  state = SubBytes(state, SRInv)
  return state

def finalRound(state, key, round):
  state = SubBytes(state, SR)
  debug("R[%d].s_box" % round,  state)
  state = ShiftRows(state, 1)
  debug("R[%d].s_row" % round,  state)
  state = AddRoundKey(state, key)
  debug("R[%d].k_sch" % round,  key)
  return state

def invFinalRound(state, key, round):
  state = AddRoundKey(state, key)
  debug("R[%d].k_sch" % round,  state)
  state = ShiftRows(state, -1)
  debug("R[%d].s_row" % round,  state)
  state = SubBytes(state, SRInv)
  debug("R[%d].s_box" % round,  state)
  return state

def rijndael(state, cipherKey):
  nb = len(state)
  nk = len(cipherKey)
  nr = max(nb, nk)+6
  expandedKey = keyExpansion(cipherKey, nr, nk, nb)
  debug("R[00].input", state)
  state = AddRoundKey(state, expandedKey[0:nb])
  for i in range(1, nr):
    subkey = expandedKey[nb*i:nb*(i+1)]
    state = round(state, expandedKey[nb*i:nb*(i+1)], i)
  state = finalRound(state, expandedKey[nb*(nr):nb*(nr+1)], nr)
  return stateToArray(state)

def invRijndael(state, cipherKey):
  nb = len(state)
  nk = len(cipherKey)
  nr = max(nb, nk)+6
  expandedKey = keyExpansion(cipherKey, nr, nk, nb)
  debug("R[00].input", state)
  state = invFinalRound(state, expandedKey[nb*(nr):nb*(nr+1)], nr)
  for i in range(nr-1, 0, -1):
    subkey = expandedKey[nb*i:nb*(i+1)]
    state = invRound(state, expandedKey[nb*i:nb*(i+1)], i)
  state = AddRoundKey(state, expandedKey[0:nb])
  return stateToArray(state)

def arrayToState(array):
  state = []
  if len(array)%4 != 0:
    raise StandardError
  for i in range(0, len(array)/4):
    state.append(array[i*4:(i+1)*4])
  return state

def stateToArray(state):
  array = []
  for i in state:
    for j in i:
      array.append(j)
  return array

def dumpStateHex(state):
  print "[",
  for i in state:
    print "[",
    for j in i:
      print "%2X" % j,
    print "],",
  print "]",


key = arrayToState([0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c])
msg = arrayToState([0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34])
enc = rijndael(msg, key)
dec = invRijndael(arrayToState(enc), key)
print dec

