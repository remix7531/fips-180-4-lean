# FIPS PUB 180-4 {.unnumbered .no-rule}

<hr class="heavy"/>

**FEDERAL INFORMATION PROCESSING STANDARDS PUBLICATION**

# Secure Hash Standard (SHS) {.unnumbered .no-rule}

**CATEGORY: COMPUTER SECURITY**

**SUBCATEGORY: CRYPTOGRAPHY**

<hr class="heavy"/>

Information Technology Laboratory\
National Institute of Standards and Technology\
Gaithersburg, MD 20899-8900\

This publication is available free of charge from:\
[http://dx.doi.org/10.6028/NIST.FIPS.180-4](http://dx.doi.org/10.6028/NIST.FIPS.180-4)

August 2015

![](doc-logo.png){.doc-logo}

**U.S. Department of Commerce**\
*Penny Pritzker, Secretary*

**National Institute of Standards and Technology**\
*Willie E. May, Under Secretary for Standards and Technology and Director*

---

## Foreword

The Federal Information Processing Standards Publication Series of the National Institute
of Standards and Technology (NIST) is the official series of publications relating to
standards and guidelines adopted and promulgated under the provisions of the Federal
Information Security Management Act (FISMA) of 2002.

Comments concerning FIPS publications are welcomed and should be addressed to the
Director, Information Technology Laboratory, National Institute of Standards and
Technology, 100 Bureau Drive, Stop 8900, Gaithersburg, MD 20899-8900.

Charles H. Romine, Director, Information Technology Laboratory

---

## Abstract

This standard specifies hash algorithms that can be used to generate digests of messages.
The digests are used to detect whether messages have been changed since the digests were
generated.

*Key words*: computer security, cryptography, message digest, hash function, hash
algorithm, Federal Information Processing Standards, Secure Hash Standard.

---

**Federal Information Processing Standards Publication 180-4**

August 2015

**Announcing the**

# SECURE HASH STANDARD {.unnumbered .no-rule}

Federal Information Processing Standards Publications (FIPS PUBS) are issued by the
National Institute of Standards and Technology (NIST) after approval by the Secretary of
Commerce pursuant to Section 5131 of the Information Technology Management Reform Act of
1996 (Public Law 104-106), and the Computer Security Act of 1987 (Public Law 100-235).

1. **Name of Standard:** Secure Hash Standard (SHS) (FIPS PUB 180-4).

2. **Category of Standard:** Computer Security Standard, Cryptography.

3. **Explanation:** This Standard specifies secure hash algorithms - SHA-1, SHA-224,
   SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 - for computing a condensed
   representation of electronic data (message). When a message of any length less than
   $2^{64}$ bits (for SHA-1, SHA-224 and SHA-256) or less than $2^{128}$ bits (for
   SHA-384, SHA-512, SHA-512/224 and SHA-512/256) is input to a hash algorithm, the
   result is an output called a message digest. The message digests range in length from
   160 to 512 bits, depending on the algorithm. Secure hash algorithms are typically used
   with other cryptographic algorithms, such as digital signature algorithms and
   keyed-hash message authentication codes, or in the generation of random numbers
   (bits).

   The hash algorithms specified in this Standard are called secure because, for a given
   algorithm, it is computationally infeasible 1) to find a message that corresponds to a
   given message digest, or 2) to find two different messages that produce the same
   message digest. Any change to a message will, with a very high probability, result in
   a different message digest. This will result in a verification failure when the secure
   hash algorithm is used with a digital signature algorithm or a keyed-hash message
   authentication algorithm.

   This Standard supersedes FIPS 180-3 [FIPS 180-3].

4. **Approving Authority:** Secretary of Commerce.

5. **Maintenance Agency:** U.S. Department of Commerce, National Institute of Standards
   and Technology (NIST), Information Technology Laboratory (ITL).

6. **Applicability:** This Standard is applicable to all Federal departments and agencies
   for the protection of sensitive unclassified information that is not subject to Title
   10 United States Code Section 2315 (10 USC 2315) and that is not within a national
   security system as defined in Title 40 United States Code Section 11103(a)(1) (40 USC
   11103(a)(1)). Either this Standard or Federal Information Processing Standard (FIPS)
   202 must be implemented wherever a secure hash algorithm is required for Federal
   applications, including as a component within other cryptographic algorithms and
   protocols. This Standard may be adopted and used by non-Federal Government
   organizations.

7. **Specifications:** Federal Information Processing Standard (FIPS) 180-4, Secure Hash
   Standard (SHS) (affixed).

8. **Implementations:** The secure hash algorithms specified herein may be implemented
   in software, firmware, hardware or any combination thereof. Only algorithm
   implementations that are validated by NIST will be considered as complying with this
   standard. Information about the validation program can be obtained at
   [http://csrc.nist.gov/groups/STM/index.html](http://csrc.nist.gov/groups/STM/index.html).

9. **Implementation Schedule:** Guidance regarding the testing and validation to FIPS
   180-4 and its relationship to FIPS 140-2 can be found in IG 1.10 of the Implementation
   Guidance for FIPS PUB 140-2 and the Cryptographic Module Validation Program at
   [http://csrc.nist.gov/groups/STM/cmvp/index.html](http://csrc.nist.gov/groups/STM/cmvp/index.html).

10. **Patents:** Implementations of the secure hash algorithms in this standard may be
    covered by U.S. or foreign patents.

11. **Export Control:** Certain cryptographic devices and technical data regarding them
    are subject to Federal export controls. Exports of cryptographic modules implementing
    this standard and technical data regarding them must comply with these Federal
    regulations and be licensed by the Bureau of Export Administration of the U.S.
    Department of Commerce. Information about export regulations is available at:
    [http://www.bis.doc.gov/index.htm](http://www.bis.doc.gov/index.htm).

12. **Qualifications:** While it is the intent of this Standard to specify general
    security requirements for generating a message digest, conformance to this Standard
    does not assure that a particular implementation is secure. The responsible
    authority in each agency or department shall assure that an overall implementation
    provides an acceptable level of security. This Standard will be reviewed every five
    years in order to assess its adequacy.

13. **Waiver Procedure:** The Federal Information Security Management Act (FISMA) does
    not allow for waivers to a FIPS that is made mandatory by the Secretary of Commerce.

14. **Where to Obtain Copies of the Standard:** This publication is available
    electronically by accessing
    [http://csrc.nist.gov/publications/](http://csrc.nist.gov/publications/). Other
    computer security publications are available at the same web site.

---

**Federal Information**\
**Processing Standards Publication 180-4**\
**Specifications for the**\

# SECURE HASH STANDARD  {.unnumbered .no-rule}

**Table of Contents**

::: toc
:::

# 1. INTRODUCTION

This Standard specifies secure hash algorithms, SHA-1, SHA-224, SHA-256, SHA-384,
SHA-512, SHA-512/224 and SHA-512/256. All of the algorithms are iterative, one-way hash
functions that can process a message to produce a condensed representation called a
*message digest*. These algorithms enable the determination of a message's integrity:
any change to the message will, with a very high probability, result in a different
message digest. This property is useful in the generation and verification of digital
signatures and message authentication codes, and in the generation of random numbers
or bits.

Each algorithm can be described in two stages: preprocessing and hash computation.
Preprocessing involves padding a message, parsing the padded message into *m*-bit blocks,
and setting initialization values to be used in the hash computation. The hash
computation generates a *message schedule* from the padded message and uses that
schedule, along with functions, constants, and word operations to iteratively generate a
series of hash values. The final hash value generated by the hash computation is used to
determine the message digest.

The algorithms differ most significantly in the security strengths that are provided for
the data being hashed. The security strengths of these hash functions and the system as
a whole when each of them is used with other cryptographic algorithms, such as digital
signature algorithms and keyed-hash message authentication codes, can be found in
[SP 800-57] and [SP 800-107].

Additionally, the algorithms differ in terms of the size of the blocks and words of data
that are used during hashing or message digest sizes. Figure 1 presents the basic
properties of these hash algorithms.

| Algorithm | Message Size (bits) | Block Size (bits) | Word Size (bits) | Message Digest Size (bits) |
|---|---|---|---|---|
| SHA-1 | $< 2^{64}$ | 512 | 32 | 160 |
| SHA-224 | $< 2^{64}$ | 512 | 32 | 224 |
| SHA-256 | $< 2^{64}$ | 512 | 32 | 256 |
| SHA-384 | $< 2^{128}$ | 1024 | 64 | 384 |
| SHA-512 | $< 2^{128}$ | 1024 | 64 | 512 |
| SHA-512/224 | $< 2^{128}$ | 1024 | 64 | 224 |
| SHA-512/256 | $< 2^{128}$ | 1024 | 64 | 256 |

**Figure 1: Secure Hash Algorithm Properties**

# 2. DEFINITIONS

## 2.1 Glossary of Terms and Acronyms

| | |
|---|---|
| **Bit** | A binary digit having a value of 0 or 1. |
| **Byte** | A group of eight bits. |
| **FIPS** | Federal Information Processing Standard. |
| **NIST** | National Institute of Standards and Technology. |
| **SHA** | Secure Hash Algorithm. |
| **SP** | Special Publication. |
| **Word** | A group of either 32 bits (4 bytes) or 64 bits (8 bytes), depending on the secure hash algorithm. |

## 2.2 Algorithm Parameters, Symbols, and Terms

### 2.2.1 Parameters

The following parameters are used in the secure hash algorithm specifications in this
Standard.

| | |
|---|---|
| $a, b, c, \ldots, h$ | Working variables that are the *w*-bit words used in the computation of the hash values, $H^{(i)}$. |
| $H^{(i)}$ | The $i^{th}$ hash value. $H^{(0)}$ is the *initial* hash value; $H^{(N)}$ is the *final* hash value and is used to determine the message digest. |
| $H_j^{(i)}$ | The $j^{th}$ word of the $i^{th}$ hash value, where $H_0^{(i)}$ is the left-most word of hash value $i$. |
| $K_t$ | Constant value to be used for the iteration $t$ of the hash computation. |
| $k$ | Number of zeroes appended to a message during the padding step. |
| $\ell$ | Length of the message, $M$, in bits. |
| $m$ | Number of bits in a message block, $M^{(i)}$. |
| $M$ | Message to be hashed. |
| $M^{(i)}$ | Message block $i$, with a size of $m$ bits. |
| $M_j^{(i)}$ | The $j^{th}$ word of the $i^{th}$ message block, where $M_0^{(i)}$ is the left-most word of message block $i$. |
| $n$ | Number of bits to be rotated or shifted when a word is operated upon. |
| $N$ | Number of blocks in the padded message. |
| $T$ | Temporary *w*-bit word used in the hash computation. |
| $w$ | Number of bits in a word. |
| $W_t$ | The $t^{th}$ *w*-bit word of the message schedule. |

### 2.2.2 Symbols and Operations

The following symbols are used in the secure hash algorithm specifications; each
operates on *w*-bit words.

| | |
|------|-----------|
| $\wedge$ | Bitwise AND operation. |
| $\vee$ | Bitwise OR ("inclusive-OR") operation. |
| $\oplus$ | Bitwise XOR ("exclusive-OR") operation. |
| $\neg$ | Bitwise complement operation. |
| $+$ | Addition modulo $2^w$. |
| $<<$ | Left-shift operation, where $x << n$ is obtained by discarding the left-most $n$ bits of the word $x$ and then padding the result with $n$ zeroes on the right. |
| $>>$ | Right-shift operation, where $x >> n$ is obtained by discarding the right-most $n$ bits of the word $x$ and then padding the result with $n$ zeroes on the left. |

The following operations are used in the secure hash algorithm specifications:

| | |
|------|-----------|
| $ROTL^n(x)$ | The *rotate left* (circular left shift) operation, where $x$ is a *w*-bit word and $n$ is an integer with $0 \leq n < w$, is defined by $ROTL^n(x) = (x << n) \vee (x >> w - n)$. |
| $ROTR^n(x)$ | The *rotate right* (circular right shift) operation, where $x$ is a *w*-bit word and $n$ is an integer with $0 \leq n < w$, is defined by $ROTR^n(x) = (x >> n) \vee (x << w - n)$. |
| $SHR^n(x)$ | The *right shift* operation, where $x$ is a *w*-bit word and $n$ is an integer with $0 \leq n < w$, is defined by $SHR^n(x) = x >> n$. |
