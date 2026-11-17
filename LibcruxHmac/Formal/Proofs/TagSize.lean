import LibcruxHmac.Formal.Specs.Defs.Hmac

/-!
# `libcrux_hmac::tag_size` (crates/algorithms/hmac/src/hmac.rs lines 63–70)

Extracted as `libcrux_hmac.tag_size` (`LibcruxHmac/Extraction/LibcruxHmac.lean`
lines 1818–1825).

natural language description:
    `tag_size(alg)` is the length in bytes of the full HMAC tag for `alg`:
    32 for SHA-256, 48 for SHA-384 and 64 for SHA-512, the digest lengths of
    these hash functions (FIPS 180-4 §1).

natural language specs:
    No preconditions. It never fails, and the result is `Spec.tagLength alg`.
    No assumption is used: `tag_size` calls nothing.
-/

open Aeneas Aeneas.Std Result WP

namespace libcrux_hmac

/-- `tag_size alg` returns the full tag length of `alg`. -/
@[step]
theorem tag_size_spec (alg : Algorithm) :
    tag_size alg ⦃ n => n.val = Spec.tagLength alg ⦄ := by
  sorry

end libcrux_hmac
