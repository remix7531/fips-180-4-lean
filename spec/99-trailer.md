# 7. TRUNCATION OF A MESSAGE DIGEST

Some application may require a hash function with a message digest length different
than those provided by the hash functions in this Standard. In such cases, a truncated
message digest may be used, whereby a hash function with a larger message digest length
is applied to the data to be hashed, and the resulting message digest is truncated by
selecting an appropriate number of the leftmost bits. For guidelines on choosing the
length of the truncated message digest and information about its security implications
for the cryptographic application that uses it, see SP 800-107 [SP 800-107].

# APPENDIX A: Additional Information

## A.1 Security of the Secure Hash Algorithms

The security of the five hash algorithms, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512,
SHA-512/224 and SHA-512/256 is discussed in [SP 800-107].

## A.2 Implementation Notes

Examples of SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 are
available at
[http://csrc.nist.gov/groups/ST/toolkit/examples.html](http://csrc.nist.gov/groups/ST/toolkit/examples.html).

## A.3 Object Identifiers

Object identifiers (OIDs) for the SHA-1, SHA-224, SHA-256, SHA-384, SHA-512,
SHA-512/224 and SHA-512/256 algorithms are posted at
[http://csrc.nist.gov/groups/ST/crypto_apps_infra/csor/algorithms.html](http://csrc.nist.gov/groups/ST/crypto_apps_infra/csor/algorithms.html).

# APPENDIX B: REFERENCES

**[FIPS 180-3]**
: NIST, Federal Information Processing Standards Publication 180-3, *Secure Hash Standards (SHS)*, October 2008.

**[SP 800-57]**
: NIST Special Publication (SP) 800-57, Part 1, *Recommendation for Key Management: General*, (Draft) May 2011.

**[SP 800-107]**
: NIST Special Publication (SP) 800-107, *Recommendation for Applications Using Approved Hash Algorithms*, (Revised), (Draft) September 2011.

# APPENDIX C: Technical Changes from FIPS 180-3

1. In FIPS 180-3, padding was inserted before hash computation begins. FIPS 140-4
   removed this restriction. Padding can be inserted before hash computation begins or
   at any other time during the hash computation prior to processing the message
   block(s) containing the padding.

2. FIPS 180-4 adds two additional algorithms: SHA-512/224 and SHA-512/256 to the
   Standard and the method for determining the initial value for SHA-512/*t* for a
   given value of *t*.

# ERRATUM

The following change has been incorporated into FIPS 180-4, as of the date indicated in
the table.

| DATE | TYPE | CHANGE | PAGE NUMBER |
|------|------|--------|-------------|
| 5/9/2014 | Editorial | Change "$t < 79$" to "$t \le 79$" | Page 10, Section 4.1.1, Line 1 |
