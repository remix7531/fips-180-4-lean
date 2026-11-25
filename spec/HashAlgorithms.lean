--#--
import spec.HashAlgorithms.SHA1
import spec.HashAlgorithms.SHA256
import spec.HashAlgorithms.SHA512
--#--

/-!
# 6. SECURE HASH ALGORITHMS

In the following sections, the hash algorithms are not described in ascending order of
size. SHA-256 is described before SHA-224 because the specification for SHA-224 is
identical to SHA-256, except that different initial hash values are used, and the final
hash value is truncated to 224 bits for SHA-224. The same is true for SHA-512, SHA-384,
SHA-512/224 and SHA-512/256, except that the final hash value is truncated to 224 bits
for SHA-512/224, 256 bits for SHA-512/256 or 384 bits for SHA-384.

For each of the secure hash algorithms, there may exist alternate computation methods
that yield identical results; one example is the alternative SHA-1 computation
described in Sec. 6.1.3. Such alternate methods may be implemented in conformance to
this standard.
-/
