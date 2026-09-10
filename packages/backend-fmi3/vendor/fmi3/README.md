# Official FMI headers

Unmodified headers and license from the FMI standard's **v3.0.2** release:

- https://github.com/modelica/fmi-standard/tree/v3.0.2/headers
- https://github.com/modelica/fmi-standard/blob/v3.0.2/LICENSE.txt

`SHA256SUMS` pins the downloaded bytes. The C headers use the BSD 2-Clause
license contained in `LICENSE.txt`; retain their notices. The same license
file also describes the separately licensed specification document.

The Lean signature reader consumes `fmi3FunctionTypes.h`; native compilation
checks generated definitions against `fmi3Functions.h`. The archive does not
include these headers under `sources/`: FMI 3.0.2 §2.5.1.3 requires the importer
to supply them. A copy of the license is included under `documentation/licenses/`.
