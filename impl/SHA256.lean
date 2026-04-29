/-!
# SHA-256 — implementation-shaped intermediate layer

A pure-Lean implementation of SHA-256.  Public surface: `toU32s`,
`compress`, `sha256`.  All loops are written as `Fin.foldl` over
`Vector UInt32 _` and `ByteArray`, keeping the file inside total
functions and free of monadic state.
-/

namespace SHS.SHA256.Impl

/-! ## Constants (FIPS-180-4 §4.2.2 and §5.3.3) -/

/-- Initial hash value for SHA-256 (FIPS-180-4 §5.3.3). -/
def H256_256 : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-- Round constants for SHA-256 (FIPS-180-4 §4.2.2). -/
def K32 : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-! ## Bit-twiddling helpers -/

/-- Circular right rotation on `UInt32` (not in core stdlib). -/
@[inline] def UInt32.rotr (x : UInt32) (n : UInt32) : UInt32 :=
  UInt32.ofBitVec (x.toBitVec.rotateRight n.toNat)

/-! ## Working types -/

/-- Working state `(a, b, c, d, e, f, g, h)`. -/
abbrev State := Vector UInt32 8

/-- Sixteen 32-bit words of one message block. -/
abbrev Block := Vector UInt32 16

/-! ## §5.2  `to_u32s` — big-endian decode of one 64-byte block -/

/-- One big-endian `UInt32` read from a 64-byte block at word index `i`. -/
@[inline] def beU32 (block : Vector UInt8 64) (i : Fin 16) : UInt32 :=
  let b0 : UInt32 := (block[4 * i.val]'(by omega)).toUInt32
  let b1 : UInt32 := (block[4 * i.val + 1]'(by omega)).toUInt32
  let b2 : UInt32 := (block[4 * i.val + 2]'(by omega)).toUInt32
  let b3 : UInt32 := (block[4 * i.val + 3]'(by omega)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Sixteen big-endian `UInt32`s from a 64-byte block. -/
def toU32s (block : Vector UInt8 64) : Block :=
  Vector.ofFn (fun i => beU32 block i)

/-! ## §6.2  Compression — 64 rounds with an inlined ring-buffer schedule -/

/-- 64-round compression function. The schedule `W` is computed lazily
into a 16-word ring buffer, reusing the input `block` storage. -/
def compress (state : State) (block : Block) : State :=
  let init : Block × State := (block, state)
  let (_, s') := Fin.foldl 64 (fun acc (i : Fin 64) =>
    let block := acc.1
    let s     := acc.2
    let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
    let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
    -- Schedule step (compute / read W[i] into the ring buffer).
    let (block', w) :=
      if hi : i.val < 16 then
        (block, block[i.val]'hi)
      else
        let w15 := block[(i.val - 15) % 16]'(by omega)
        let s0  := (UInt32.rotr w15 7) ^^^ (UInt32.rotr w15 18) ^^^ (w15 >>> 3)
        let w2  := block[(i.val - 2) % 16]'(by omega)
        let s1  := (UInt32.rotr w2 17) ^^^ (UInt32.rotr w2 19) ^^^ (w2 >>> 10)
        let w16 := block[(i.val - 16) % 16]'(by omega)
        let w7  := block[(i.val - 7) % 16]'(by omega)
        let new := w16 + s0 + w7 + s1
        (block.set ((i.val) % 16) new (by omega), new)
    -- Round step (mix `w` into the eight working variables).
    let s1 := (UInt32.rotr e 6) ^^^ (UInt32.rotr e 11) ^^^ (UInt32.rotr e 25)
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := s1 + ch + K32[i] + w + h
    let s0 := (UInt32.rotr a 2) ^^^ (UInt32.rotr a 13) ^^^ (UInt32.rotr a 22)
    let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + mj
    let s' : State := #v[t1 + t2, a, b, c, d + t1, e, f, g]
    (block', s')) init
  Vector.zipWith (· + ·) state s'

/-! ## §6.2  Top-level `sha256` -/

/-- Streaming-padded SHA-256 of `data`.

FIPS 180-4 §5.1.1 caps the input bit-length at `2 ^ 64 - 1`, so byte-oriented
SHA-256 is only defined for `data.size < 2 ^ 61`.  Beyond that bound,
`data.size.toUInt64 <<< 3` would silently wrap and produce a wrong digest.
We refuse with `panic!` instead.  The verified-correctness theorem
`SHS.Equiv.SHA256.sha256_correct` carries `data.size < 2 ^ 61` as a
precondition, so the panic branch is unreachable inside the verified region. -/
def sha256 (data : ByteArray) : Vector UInt8 32 :=
  if 2 ^ 61 ≤ data.size then
    panic! s!"SHS.SHA256.Impl.sha256: input size {data.size} bytes exceeds FIPS 180-4 §5.1.1 limit (2^61 bytes)"
  else
  let blocks    := data.size / 64
  let remaining := data.size % 64
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  -- Process complete blocks.
  let state : State := Fin.foldl blocks (fun state (i : Fin blocks) =>
    let block : Vector UInt8 64 := Vector.ofFn fun j : Fin 64 =>
      data.get! (i.val * 64 + j.val)
    compress state (toU32s block)) H256_256
  -- Process the final block(s) with padding.
  let finalBlockA : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < remaining then data.get! (blocks * 64 + i.val)
    else if i.val = remaining then 0x80
    else 0
  -- If we don't have room for the length, compress this block and start fresh.
  let (state, finalBlockB) :=
    if remaining < 56 then (state, finalBlockA)
    else
      (compress state (toU32s finalBlockA),
       Vector.ofFn (fun _ : Fin 64 => (0 : UInt8)))
  -- Append the bit-length in big-endian to the last 8 bytes.
  let finalBlockC : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < 56 then finalBlockB[i]
    else ((totalBits >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
  let state := compress state (toU32s finalBlockC)
  -- Convert state to output bytes (big-endian).
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

end SHS.SHA256.Impl
