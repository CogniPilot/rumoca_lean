# Pinned eFMI schemas

`schemas/` is the unmodified `xml-schema-definitions/` directory from the
official [eFMI 1.0.0 Beta 1 release archive](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The archive SHA-256 is
`da5caf207aca412b5601cafaaf72d4e613d1c78964e3f39afc6a5a3d06281a89`.
`SHA256SUMS` records every extracted file, including its original line endings.
The upstream BSD 3-Clause license is preserved at `schemas/LICENSE`.

These are schema resources and an independent interoperability check, not a
Lean proof of XSD semantics or complete eFMI compliance. Formal binding of
these exact resources into the certified archive remains an E05 obligation.
The specification's prose/schema discrepancies are recorded in `dev/efmi.md`.
