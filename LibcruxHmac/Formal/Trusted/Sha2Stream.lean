import LibcruxHmac.Formal.Specs.Defs.Stream

/-!
# Trusted (boundary A2): the libcrux-sha2 streaming digests

**Boundary A2 (rc1-only exception).** The streaming hash states
`libcrux_sha2::impl_hacl::{Sha256, Sha384, Sha512}` and their digest-trait
operations `new`, `update` and `finish` are not extracted. Aeneas emits them as
axioms that give only a type (`LibcruxHmac/Extraction/LibcruxHmac.lean`
lines 245–604). The owner accepted A2 as an assumption on 2026-11-15
(`.formalising/auto-fv/externals.json`, record `a2-libcrux-sha2-impl-hacl`).

Each axiom below assumes one `DigestContract` (`Defs/Stream.lean`): the state
behaves like the bytes absorbed so far, `update` rejects a single input over
`u32::MAX` bytes, and `finish` returns the FIPS 180-4 hash of the absorbed bytes.
The total limit is the one HACL enforces (`sha256StreamMax`, `sha512StreamMax`).
An update that would pass it returns `Ok(())` and leaves the state unchanged: the
input is silently dropped (law `update_full`; HACL `hacl.rs` lines 665–669 and
972–976 return `MaximumLengthExceeded` before changing the state, `impl_hacl.rs`
lines 110–112 discard that code, `impl_digest_trait.rs` lines 54–60 return `Ok`).

`reset` is not covered: the HMAC code does not call it.

A model exists: take the state to be the list of absorbed bytes (at most the
limit), `Represents s m` to be `s = m`, and an update past the limit to be the
identity. Each axiom constrains its own opaque state type and operations.
-/

open libcrux_hmac.Spec

namespace libcrux_hmac.Trusted

/-- A2, `a2-libcrux-sha2-impl-hacl`: the SHA-256 streaming digest
(`libcrux_sha2::Sha256Hash` with state `impl_hacl::Sha256`) computes SHA-256 of
what it absorbs, up to `2 ^ 61 - 1` bytes in total; it drops input past that. -/
axiom sha256Contract : DigestContract sha256Digest sha256Init sha256 sha256StreamMax

/-- A2, `a2-libcrux-sha2-impl-hacl`: the SHA-384 streaming digest
(`libcrux_sha2::Sha384Hash` with state `impl_hacl::Sha384`) computes SHA-384 of
what it absorbs, up to `2 ^ 64 - 1` bytes in total; it drops input past that. -/
axiom sha384Contract : DigestContract sha384Digest sha384Init sha384 sha512StreamMax

/-- A2, `a2-libcrux-sha2-impl-hacl`: the SHA-512 streaming digest
(`libcrux_sha2::Sha512Hash` with state `impl_hacl::Sha512`) computes SHA-512 of
what it absorbs, up to `2 ^ 64 - 1` bytes in total; it drops input past that. -/
axiom sha512Contract : DigestContract sha512Digest sha512Init sha512 sha512StreamMax

end libcrux_hmac.Trusted
