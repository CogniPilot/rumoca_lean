# SHA-1 in Lean

Independent raw-byte SHA-1 implementation, proofs and proof-producing checksum
certificates. Import `SHA1` for runtime definitions in `SHA1`,
`SHA1.Proofs` for padding/digest properties, or
`SHA1.CertificateCheck` for actual-string certificates.

The Lake package name is `sha1`; the public module and namespace root is `SHA1`.

The implementation uses Lean's standard library. Its check library additionally
uses the local `verification` package to enforce the existing axiom whitelist.
It has no parser, compiler, mathlib, FMI or eFMI dependency.

From the repository root inside `nix develop`:

```sh
lake build check-sha1
lake build sha1/SHA1.CertificateProofs
```

`lake -d packages/sha1 test` also works as a standalone check. The package owns
the existing empty-message and NIST example certificates and all SHA-1 axiom
audits. Lake caches these independently of the compiler's checks.

The certificate builder proposes bytes and intermediate states with native
evaluation, then constructs kernel-checked proofs for the original UTF-8
string, its byte count and padding, every compression block, and the final
digest. The caller must audit the generated theorem's complete dependencies.
No native-reduction proof axiom or external hash library is used.

These theorems concern the authored FIPS 180-4 algorithm. Correspondence with
the prose standard remains a review obligation; no collision resistance or
authentication guarantee is claimed. eFMI uses this package for its specified
integrity fields. XML, manifest references, file I/O and archive binding belong
to their respective consumers.
