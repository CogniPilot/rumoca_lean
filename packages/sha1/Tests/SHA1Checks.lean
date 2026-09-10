import SHA1.Proofs
import SHA1.CertificateProofs
import ProofAudit.Audit

/-! Published NIST one- and two-block examples, plus the empty-message
boundary. These are regression certificates, not a proof of cryptographic
security or a replacement for the authored FIPS algorithm review. -/
namespace SHA1Checks

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem empty : SHA1.hash "".toUTF8 = "da39a3ee5e6b4b0d3255bfef95601890afd80709" := by decide +kernel
theorem abc : SHA1.hash "abc".toUTF8 = "a9993e364706816aba3e25717850c26c9cd0d89d" := by decide +kernel
theorem two_blocks :
    SHA1.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 =
      "84983e441c3bd26ebaae4aa1f95129e5e54670f1" := by decide +kernel

#audit axioms SHA1.pad_aligned
#audit axioms SHA1.pad_nonempty
#audit axioms SHA1.digest_bytes_length
#audit axioms empty
#audit axioms abc
#audit axioms two_blocks

#audit axioms SHA1.foldBlocks_zero
#audit axioms SHA1.foldBlocksUsing_succ
#audit axioms SHA1.Certificate.checkBlocks_sound
#audit axioms SHA1.Certificate.check_of_padding
#audit axioms SHA1.Certificate.utf8_of_chars
#audit axioms SHA1.Certificate.pad_of_length
#audit axioms SHA1.Certificate.append_suffix
#audit axioms SHA1.Certificate.block_cons
#audit axioms SHA1.Certificate.hash_of_blocks
#audit axioms SHA1.Certificate.hash_correct
#audit axioms SHA1.Certificate.build_checked

end SHA1Checks
