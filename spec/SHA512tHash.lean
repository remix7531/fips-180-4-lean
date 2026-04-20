--#--
import spec.SHA512t
set_option autoImplicit true
--#--

namespace SHS --#

/-!
## 6.6 SHA-512/224

SHA-512/224 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm is defined in the exact same manner as SHA-512
(Sec. 6.4), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.6.1; and
2. The 224-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 224 bits.
-/

namespace SHA512 --#

def sha512_224 (M : Message) (_h : M.length < 2 ^ 128) : Digest 224 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_512_224
  -- truncate H^(N) to its left-most 224 bits
  (H[0]! ++ H[1]! ++ H[2]! ++ H[3]!).leftmost 224

end SHA512 --#

/-!
## 6.7 SHA-512/256

SHA-512/256 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm is defined in the exact same manner as SHA-512
(Sec. 6.4), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.6.2; and
2. The 256-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 256 bits.
-/

namespace SHA512 --#

def sha512_256 (M : Message) (_h : M.length < 2 ^ 128) : Digest 256 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_512_256
  H[0]! ++ H[1]! ++ H[2]! ++ H[3]!

end SHA512 --#

end SHS --#
