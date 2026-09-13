/-! Typedef spellings shared by the runtime's certified function printers.
These names describe a syntax context, not native ABI/type meanings. Keeping
the vocabulary independent lets component printers compose without cycles. -/
namespace Rumoca.FMI3.RuntimePrinter

def typedefs : List String :=
  ["Instance", "Model", "size_t", "uint64_t", "fmi3Instance", "fmi3InstanceEnvironment",
    "fmi3FMUState", "fmi3ValueReference", "fmi3Float32", "fmi3Float64",
    "fmi3Int8", "fmi3UInt8", "fmi3Int16", "fmi3UInt16", "fmi3Int32", "fmi3UInt32",
    "fmi3Int64", "fmi3UInt64", "fmi3Boolean", "fmi3Char", "fmi3String", "fmi3Byte",
    "fmi3Binary", "fmi3Clock", "fmi3Status", "fmi3DependencyKind", "fmi3IntervalQualifier",
    "fmi3LogMessageCallback", "fmi3ClockUpdateCallback", "fmi3IntermediateUpdateCallback",
    "fmi3LockPreemptionCallback", "fmi3UnlockPreemptionCallback", "atomic_bool"]

end Rumoca.FMI3.RuntimePrinter
