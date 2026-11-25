--#--
import spec.Preprocessing
import spec.HashAlgorithms.Bounds

set_option autoImplicit true
open scoped SHS.HashAlgorithmBounds
--#--

namespace SHS --#
/-!
## 6.4 SHA-512

SHA-512 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm uses 1) a message schedule of eighty 64-bit words,
2) eight working variables of 64 bits each, and 3) a hash value of eight 64-bit words.
The final result of SHA-512 is a 512-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{79}$. The eight
working variables are labeled $a$, $b$, $c$, $d$, $e$, $f$, $g$, and $h$. The words of
the hash value are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_7^{(i)}$, which will hold
the initial hash value, $H^{(0)}$, replaced by each successive intermediate hash value
(after each message block is processed), $H^{(i)}$, and ending with the final hash
value, $H^{(N)}$. SHA-512 also uses two temporary words, $T_1$ and $T_2$.

### 6.4.1 SHA-512 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.5.
2. The message is padded and parsed as specified in Section 5.

### 6.4.2 SHA-512 Hash Computation

The SHA-512 hash computation uses functions and constants previously defined in
Sec. 4.1.3 and Sec. 4.2.3, respectively. Addition ($+$) is performed modulo $2^{64}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order,
using the following steps:
-/

namespace SHA512 --#

/-- FIPS-180-4 §6.4.2 step 1: SHA-512 message schedule (16-word block → 80 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 80 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 79: W_t = σ_1^(512)(W_{t-2}) + W_{t-7} + σ_0^(512)(W_{t-15}) + W_{t-16}
  for h : t in [16:80] do
    W[t] := smallSigma1 W[t-2] + W[t-7] + smallSigma0 W[t-15] + W[t-16]
  W

/-!  -/

/-- FIPS-180-4 §6.4.2 steps 2-4: SHA-512 block compression updating the 8-word state. -/ --#
def compress (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. Prepare the message schedule {W_t}
  let W := schedule M
  -- Step 2. Initialize the eight working variables a..h with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  let mut f := H[5]
  let mut g := H[6]
  let mut h := H[7]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let T1 := h + bigSigma1 e + Ch e f g + K[t] + W[t]
    let T2 := bigSigma0 a + Maj a b c
    h := g
    g := f
    f := e
    e := d + T1
    d := c
    c := b
    b := a
    a := T1 + T2
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[
    a + H[0], b + H[1], c + H[2], d + H[3],
    e + H[4], f + H[5], g + H[6], h + H[7]
  ]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 512-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)} \|
  H_6^{(N)} \| H_7^{(N)}$$
-/

/-- FIPS-180-4 §6.4: SHA-512 hash of a message `M` (length < 2¹²⁸ bits) → 512-bit digest. -/ --#
def sha512 (M : Message) (_h : M.length < 2 ^ 128) : Digest 512 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_512
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6] ++ H[7]

end SHA512 --#

/-!
## 6.5 SHA-384

SHA-384 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm is defined in the exact same manner as SHA-512
(Sec. 6.4), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.4; and
2. The 384-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 384 bits:

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)}$$
-/

namespace SHA512 --#

/-- FIPS-180-4 §6.5: SHA-384 hash — SHA-512 with `H0_384` IV, truncated to 384 bits. -/ --#
def sha384 (M : Message) (_h : M.length < 2 ^ 128) : Digest 384 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_384
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5]

end SHA512 --#

end SHS --#
