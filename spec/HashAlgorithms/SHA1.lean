--#--
import spec.Preprocessing
import spec.HashAlgorithms.Bounds

set_option autoImplicit true
open scoped SHS.HashAlgorithmBounds
--#--

namespace SHS --#
/-!
## 6.1 SHA-1

SHA-1 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The algorithm uses 1) a message schedule of eighty 32-bit words,
2) five working variables of 32 bits each, and 3) a hash value of five 32-bit words.
The final result of SHA-1 is a 160-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{79}$. The five
working variables are labeled $a$, $b$, $c$, $d$, and $e$. The words of the hash value
are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_4^{(i)}$, which will hold the initial hash
value, $H^{(0)}$, replaced by each successive intermediate hash value (after each
message block is processed), $H^{(i)}$, and ending with the final hash value,
$H^{(N)}$. SHA-1 also uses a single temporary word, $T$.

### 6.1.1 SHA-1 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.1.
2. The message is padded and parsed as specified in Section 5.

### 6.1.2 SHA-1 Hash Computation

The SHA-1 hash computation uses functions and constants previously defined in
Sec. 4.1.1 and Sec. 4.2.1, respectively. Addition ($+$) is performed modulo $2^{32}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order, using
the following steps:

-/

namespace SHA1 --#

/-- FIPS-180-4 §6.1.2 step 1: SHA-1 message schedule (16-word block → 80 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 80 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 79: W_t = ROTL^1(W_{t-3} ⊕ W_{t-8} ⊕ W_{t-14} ⊕ W_{t-16})
  for h : t in [16:80] do
    W[t] := ROTL 1 (W[t-3] ⊕ W[t-8] ⊕ W[t-14] ⊕ W[t-16])
  W

/-!  -/

/-- FIPS-180-4 §6.1.2 steps 2-4: SHA-1 block compression updating the 5-word state. -/ --#
def compress (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. Prepare the message schedule {W_t}
  let W := schedule M
  -- Step 2. Initialize the five working variables a, b, c, d, e with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let T := ROTL 5 a + f t b c d + e + K t + W[t]
    e := d
    d := c
    c := ROTL 30 b
    b := a
    a := T
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[a + H[0], b + H[1], c + H[2], d + H[3], e + H[4]]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 160-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)}$$
-/

/-- FIPS-180-4 §6.1: SHA-1 hash of a message `M` (length < 2⁶⁴ bits) → 160-bit digest. -/ --#
def sha1 (M : Message) (_h : M.length < 2 ^ 64) : Digest 160 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4]

end SHA1 --#

/-!
### 6.1.3 Alternate Method for Computing a SHA-1 Message Digest

The SHA-1 hash computation method described in Sec. 6.1.2 assumes that the message
schedule $W_0, W_1, \ldots, W_{79}$ is implemented as an array of eighty 32-bit words.
This is efficient from the standpoint of the minimization of execution time, since the
addresses of $W_{t-3}, \ldots, W_{t-16}$ in step (2) of Sec. 6.1.2 are easily computed.

However, if memory is limited, an alternative is to regard $\{W_t\}$ as a circular
queue that may be implemented using an array of sixteen 32-bit words,
$W_0, W_1, \ldots, W_{15}$. The alternate method that is described in this section
yields the same message digest as the SHA-1 computation method described in Sec. 6.1.2.
Although this alternate method saves sixty-four 32-bit words of storage, it is likely
to lengthen the execution time due to the increased complexity of the address
computations for the $\{W_t\}$ in step (3).

For this alternate SHA-1 method, let $MASK = \texttt{0000000f}$ (in hex). As in
Sec. 6.1.1, addition is performed modulo $2^{32}$. Assuming that the preprocessing as
described in Sec. 6.1.1 has been performed, the processing of $M^{(i)}$ is as follows:

-/

namespace SHA1 --#

/-- FIPS-180-4 §6.1.3: SHA-1 alternate compression using a 16-word circular schedule. -/ --#
def compress_alt (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. For t = 0 to 15: W_t = M_t^(i).  Note: the SHA-1 alternate method's
  -- circular schedule has only 16 words; we therefore use `Block` (size 16) here
  -- in place of the 80-word `Schedule` used by the standard method.
  let mut W : Block := M
  -- Step 2. Initialize the five working variables a, b, c, d, e with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let s := t &&& 0xf
    if t ≥ 16 then
      W[s] := ROTL 1 (W[(s+13) % 16] ⊕ W[(s+8) % 16] ⊕ W[(s+2) % 16] ⊕ W[s])
    let T := ROTL 5 a + f t b c d + e + K t + W[s]
    e := d
    d := c
    c := ROTL 30 b
    b := a
    a := T
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[a + H[0], b + H[1], c + H[2], d + H[3], e + H[4]]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 160-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)}$$
-/

/-- FIPS-180-4 §6.1.3: SHA-1 hash via the alternate (circular schedule) method. -/ --#
def sha1_alt (M : Message) (_h : M.length < 2 ^ 64) : Digest 160 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress_alt H0
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4]

/-!
The CAVP tests exercise both `SHA1.sha1` and `SHA1.sha1_alt`. The
equivalence proofs cover the SHA-2 family. The equality of the two
SHA-1 methods remains unproved here.
-/

end SHA1 --#

end SHS --#
