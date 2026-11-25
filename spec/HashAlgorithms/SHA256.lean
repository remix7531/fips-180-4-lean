--#--
import spec.Preprocessing
import spec.HashAlgorithms.Bounds

set_option autoImplicit true
open scoped SHS.HashAlgorithmBounds
--#--

namespace SHS --#
/-!
## 6.2 SHA-256

SHA-256 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The algorithm uses 1) a message schedule of sixty-four 32-bit
words, 2) eight working variables of 32 bits each, and 3) a hash value of eight 32-bit
words. The final result of SHA-256 is a 256-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{63}$. The eight
working variables are labeled $a$, $b$, $c$, $d$, $e$, $f$, $g$, and $h$. The words of
the hash value are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_7^{(i)}$, which will hold
the initial hash value, $H^{(0)}$, replaced by each successive intermediate hash value
(after each message block is processed), $H^{(i)}$, and ending with the final hash
value, $H^{(N)}$. SHA-256 also uses two temporary words, $T_1$ and $T_2$.

### 6.2.1 SHA-256 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.3.
2. The message is padded and parsed as specified in Section 5.

### 6.2.2 SHA-256 Hash Computation

The SHA-256 hash computation uses functions and constants previously defined in
Sec. 4.1.2 and Sec. 4.2.2, respectively. Addition ($+$) is performed modulo $2^{32}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order,
using the following steps:

-/

namespace SHA256 --#

/-- FIPS-180-4 §6.2.2 step 1: SHA-256 message schedule (16-word block → 64 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 64 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 63: W_t = σ_1^(256)(W_{t-2}) + W_{t-7} + σ_0^(256)(W_{t-15}) + W_{t-16}
  for h : t in [16:64] do
    W[t] := smallSigma1 W[t-2] + W[t-7] + smallSigma0 W[t-15] + W[t-16]
  W

/-!  -/

/-- FIPS-180-4 §6.2.2 steps 2-4: SHA-256 block compression updating the 8-word state. -/ --#
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
  -- Step 3. For t = 0 to 63
  for h : t in [0:64] do
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
$M^{(N)}$), the resulting 256-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \|
  H_4^{(N)} \| H_5^{(N)} \| H_6^{(N)} \| H_7^{(N)}$$
-/

/-- FIPS-180-4 §6.2: SHA-256 hash of a message `M` (length < 2⁶⁴ bits) → 256-bit digest. -/ --#
def sha256 (M : Message) (_h : M.length < 2 ^ 64) : Digest 256 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_256
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6] ++ H[7]

end SHA256 --#

/-!
## 6.3 SHA-224

SHA-224 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The function is defined in the exact same manner as SHA-256
(Section 6.2), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.2; and
2. The 224-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 224 bits:

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)} \| H_6^{(N)}$$
-/

namespace SHA256 --#

/-- FIPS-180-4 §6.3: SHA-224 hash — SHA-256 with `H0_224` IV, truncated to 224 bits. -/ --#
def sha224 (M : Message) (_h : M.length < 2 ^ 64) : Digest 224 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_224
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6]

end SHA256 --#

end SHS --#
