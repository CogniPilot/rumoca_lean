# XML output in Lean

Independent XML tree representation, renderer, restricted output syntax and
correctness proofs. Import `XML` for the renderer in `XML`,
`XML.Syntax` for the independent output relation and validator, or
`XML.Proofs` for escaping, attribute, element and document theorems.

The Lake package name is `xml`; the public module and namespace root is `XML`.

`XML.Certificate` supplies compositional renderer equalities.
`XML.CertificateCheck` quotes candidate trees and constructs proofs that their
complete documents equal supplied strings. It checks each element, composes
the character lists, and checks the connection to a flat literal before using
the standard library's string/list correspondence. Native evaluation proposes
data; the kernel checks every equality. Consumers audit the final theorem.
`certifyValidity` separately certifies the restricted output profile by
composing per-element header checks and child validity proofs.

The implementation and proofs use Lean's standard library. The check library
uses the local `verification` package for the existing axiom whitelist. There
is no compiler, parser, mathlib, SHA-1, FMI or eFMI dependency.

From the repository root inside `nix develop`:

```sh
lake build check-xml
lake build xml/XML.Proofs
```

`lake -d packages/xml test` also runs its independent check library. The XML
audit roots moved here from the eFMI checks; no obligation was dropped.

The checked output profile has unqualified ASCII names, printable ASCII
attribute/text values, five predefined entities and element-only or text-only
content. `document_correct` proves that every tree passing `Element.valid`
renders a document in this authored syntax relation. This is not a general
XML parser, XSD validator, namespace implementation or full XML conformance
claim. FMI/eFMI document construction, schemas, manifest graphs and binding to
actual emitted files remain responsibilities of the consumers.
