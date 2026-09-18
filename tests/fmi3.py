"""Independent archive, schema, importer and raw FMI ABI regression checks.

This is test infrastructure, not compiler implementation or a formal certificate.
Run inside the Nix shell: python3 tests/fmi3.py MODEL.fmu SECOND_MODEL.fmu

A second entry point, `python3 tests/fmi3.py --matrix MODEL.fmu LABEL`, drives the
raw FMI 3 ABI over every one of the 75 emitted public functions and asserts the
documented status and logger callbacks for each behavior class the compiler
proves: null handle, lifecycle rejection, argument rejection, communication-step
discard, suppressed versus enabled logging, capability rejection, and the empty
versus non-empty absent-typed accessors. It exists so that every behavior class
recorded as proof-only is also instantiated natively at least once. If a native
observation ever differs from the proved status the run fails and reports the
exact discrepancy rather than weakening the assertion.
"""

import ctypes as C
import math
from pathlib import Path, PurePosixPath
import re
import shlex
import struct
import subprocess
import sys
import tempfile
import unittest
import zipfile
from xml.etree import ElementTree

from fmpy import read_model_description, simulate_fmu
from fmpy.validation import validate_fmu
from fmpy.model_description import read_build_description


D, B, N, VR, P = C.c_double, C.c_bool, C.c_size_t, C.c_uint32, C.c_void_p
I32 = C.c_int32
OK, DISCARD, ERROR = 0, 2, 3
LOG = C.CFUNCTYPE(None, P, C.c_int, C.c_char_p, C.c_char_p)

# The 25 capability-rejected functions (return fmi3Error, log the shared message
# when enabled, and read no argument beyond the instance handle).
CAPABILITY = [
    "GetClock", "SetClock", "GetNumberOfVariableDependencies", "GetVariableDependencies",
    "GetFMUState", "SetFMUState", "FreeFMUState", "SerializedFMUStateSize",
    "SerializeFMUState", "DeserializeFMUState", "GetDirectionalDerivative",
    "GetAdjointDerivative", "EnterConfigurationMode", "ExitConfigurationMode",
    "GetIntervalDecimal", "GetIntervalFraction", "GetShiftDecimal", "GetShiftFraction",
    "SetIntervalDecimal", "SetIntervalFraction", "SetShiftDecimal", "SetShiftFraction",
    "EnterStepMode", "GetOutputDerivatives", "ActivateModelPartition",
]
CAPABILITY_MESSAGE = b"FMI capability is not supported"

# The 12 absent-typed families, each with a get and a set accessor. Binary carries
# an extra value-sizes pointer between the references and the values.
ABSENT_TYPES = [
    "Float32", "Int8", "UInt8", "Int16", "UInt16", "Int32", "UInt32",
    "Int64", "UInt64", "Boolean", "String", "Binary",
]
BINARY_TYPES = {"Binary"}
ABSENT_FUNCS = ["Get" + t for t in ABSENT_TYPES] + ["Set" + t for t in ABSENT_TYPES]
ABSENT_MESSAGE = b"No variables of this type exist"
LIFECYCLE_MESSAGE = b"Call is not allowed in the current FMI state"

# The 21 model-facing functions that return fmi3Status and take an instance handle.
MODEL_STATUS = [
    "SetDebugLogging", "EnterInitializationMode", "ExitInitializationMode", "Reset",
    "GetNumberOfContinuousStates", "GetNumberOfEventIndicators",
    "GetNominalsOfContinuousStates", "GetContinuousStates", "SetContinuousStates",
    "GetContinuousStateDerivatives", "GetFloat64", "SetFloat64", "Terminate",
    "SetTime", "EnterEventMode", "EnterContinuousTimeMode", "CompletedIntegratorStep",
    "UpdateDiscreteStates", "DoStep", "GetEventIndicators", "EvaluateDiscreteStates",
]

# Every status-returning function that accepts a handle, for the null-handle sweep.
NULL_SWEEP = MODEL_STATUS + ABSENT_FUNCS + CAPABILITY  # 70 of the 75

# Native observations that already differ from the standard-conformant scalar
# behavior and are recorded as findings in dev/trust-ledger.md. A cell listed
# here is still exercised and reported, but does not fail the run; any divergence
# not listed here is a regression and does fail the run. Keyed by matrix label.
# Both adapters now conform on every exercised cell, so the allowlist is empty:
# the matrix asserts conforming behavior on the scalar and the tensor FMU alike.
KNOWN_DISCREPANCIES = {}


def _matrix_config(md):
    """Value references and cardinalities used by the model-facing cells."""
    name = md.modelName
    if name == "Integrator":
        return dict(input_vr=1, input_n=1, start=[0.5], n_states=1, get_vr=1, get_n=1)
    if name == "TensorSquare":
        return dict(input_vr=1, input_n=2, start=[1.0, 2.0], n_states=2, get_vr=2, get_n=2)
    raise SystemExit("behavior matrix: unsupported model " + name)


def behavior_matrix(fmu_path, label):
    """Instantiate every proved behavior class natively over all 75 functions.

    Returns (functions_touched, behavior_cells, discrepancies). A discrepancy is a
    native status or callback that differs from the proved behavior; the caller
    fails the run and reports it rather than relaxing the expectation.
    """
    root = Path(tempfile.mkdtemp(prefix="rumoca-matrix-"))
    with zipfile.ZipFile(fmu_path) as archive:
        for entry in archive.infolist():
            member = PurePosixPath(entry.filename)
            if member.is_absolute() or ".." in member.parts or "\\" in entry.filename:
                raise ValueError("unsafe FMU member")
        archive.extractall(root)
    md = read_model_description(fmu_path, validate=True)
    dll = C.CDLL(str(next((root / "binaries").glob("*-linux/*.so"))))
    cfg = _matrix_config(md)
    token = md.instantiationToken.encode()
    n_states = cfg["n_states"]

    messages = []
    logger = LOG(lambda env, status, category, message:
                 messages.append((env, status, category, message)))
    funcs = set()
    cells = [0]
    discrepancies = []

    def touch(*names):
        funcs.update(names)

    def check(condition, description):
        cells[0] += 1
        if not condition:
            discrepancies.append(description)

    def fn(name, argtypes, restype=C.c_int):
        # Build an independent bound function so distinct call sites (for example
        # the null-handle sweep and the typed success path) never share argtypes.
        return C.CFUNCTYPE(restype, *argtypes)(("fmi3" + name, dll))

    inst_cs = fn("InstantiateCoSimulation",
                 [C.c_char_p, C.c_char_p, C.c_char_p, B, B, B, B, C.POINTER(VR), N, P, LOG, P], P)
    inst_me = fn("InstantiateModelExchange", [C.c_char_p, C.c_char_p, C.c_char_p, B, B, P, LOG], P)
    inst_se = fn("InstantiateScheduledExecution",
                 [C.c_char_p, C.c_char_p, C.c_char_p, B, B, P, LOG, P, P, P], P)
    free = fn("FreeInstance", [P], None)

    def cs(logging=False, tk=token):
        return inst_cs(b"m", tk, None, False, logging, False, False, None, 0, P(123), logger, None)

    def me(logging=False, tk=token):
        return inst_me(b"m", tk, None, False, logging, P(123), logger)

    do_step_fn = fn("DoStep", [P, D, D, B] + [C.POINTER(B)] * 3 + [C.POINTER(D)])

    def do_step(handle, point, size):
        flags = [B(True) for _ in range(3)]
        last = D(-99)
        return do_step_fn(handle, point, size, True, *map(C.byref, flags), C.byref(last))

    set_f64 = fn("SetFloat64", [P, C.POINTER(VR), N, C.POINTER(D), N])
    get_f64 = fn("GetFloat64", [P, C.POINTER(VR), N, C.POINTER(D), N])
    enter_init = fn("EnterInitializationMode", [P, B, D, D, B, D])
    exit_init = fn("ExitInitializationMode", [P])
    terminate = fn("Terminate", [P])
    reset = fn("Reset", [P])
    set_time = fn("SetTime", [P, D])

    def initialize(handle):
        return (enter_init(handle, False, 0.0, 0.0, False, 0.0) == OK
                and set_f64(handle, (VR * 1)(cfg["input_vr"]), 1,
                            (D * cfg["input_n"])(*cfg["start"]), cfg["input_n"]) == OK
                and exit_init(handle) == OK)

    # -- fmi3GetVersion --
    touch("GetVersion")
    version = fn("GetVersion", [], C.c_char_p)
    check(version() == b"3.0", "fmi3GetVersion should return 3.0")

    # -- instantiation success and creation-failure (the factory's null case) --
    touch("InstantiateModelExchange", "InstantiateCoSimulation",
          "InstantiateScheduledExecution", "FreeInstance")
    live_cs = cs()
    live_me = me()
    check(bool(live_cs), "co-simulation instantiation should succeed")
    check(bool(live_me), "model-exchange instantiation should succeed")
    check(not cs(tk=b"wrong-token"), "co-simulation rejects a wrong token with a null handle")
    check(not me(tk=b"wrong-token"), "model-exchange rejects a wrong token with a null handle")
    check(not inst_se(b"m", token, None, False, False, P(123), logger, None, None, None),
          "scheduled execution is unsupported and returns a null handle")
    free(None)  # fmi3FreeInstance on a null handle must be a safe no-op.
    free(live_cs)
    free(live_me)

    # -- null-handle sweep over all 70 handle-taking status functions --
    for name in NULL_SWEEP:
        touch(name)
        check(fn(name, [P])(None) == ERROR, "fmi3%s on a null handle should return fmi3Error" % name)

    # -- capability rejection: suppressed and enabled logging, both interfaces --
    for kind, make in [("co-simulation", cs), ("model-exchange", me)]:
        quiet, loud = make(False), make(True)
        for name in CAPABILITY:
            touch(name)
            rej = fn(name, [P])
            messages.clear()
            check(rej(quiet) == ERROR, "fmi3%s rejected on %s" % (name, kind))
            check(messages == [], "fmi3%s emits no callback with logging off" % name)
            messages.clear()
            check(rej(loud) == ERROR, "fmi3%s rejected on %s with logging" % (name, kind))
            check(len(messages) == 1 and messages[0][:3] == (123, ERROR, b"logStatus")
                  and messages[0][3] == CAPABILITY_MESSAGE,
                  "fmi3%s logs the capability message once" % name)
        free(quiet)
        free(loud)

    # -- absent-typed accessors: empty request accepted --
    # A non-empty request returns fmi3Error, which moves the instance into the
    # terminal error state (FMI 3.0.2 section 2.3.1), so the empty-request cells
    # (which must return fmi3OK) run first on a healthy initialized instance.
    def absent(name):
        binary = name[3:] in BINARY_TYPES
        argtypes = [P, P, N] + ([P] if binary else []) + [P, N]
        return fn(name, argtypes), ([None] if binary else [])

    healthy = cs(True)
    check(enter_init(healthy, False, 0.0, 0.0, False, 0.0) == OK,
          "absent-typed empty-request fixture initialization")
    for name in ABSENT_FUNCS:
        touch(name)
        accessor, extra = absent(name)
        messages.clear()
        check(accessor(healthy, None, 0, *extra, None, 0) == OK,
              "fmi3%s accepts an empty request" % name)
        check(messages == [], "fmi3%s empty request emits no callback" % name)
    free(healthy)

    # -- absent-typed accessors: non-empty request rejected, suppressed and
    #    enabled logging. Each rejection terminates its instance, so every
    #    non-empty cell runs on a fresh instance to observe the true message. --
    for logging in [False, True]:
        for name in ABSENT_FUNCS:
            accessor, extra = absent(name)
            handle = cs(logging)
            check(enter_init(handle, False, 0.0, 0.0, False, 0.0) == OK,
                  "absent-typed non-empty fixture initialization")
            messages.clear()
            check(accessor(handle, None, 1, *extra, None, 0) == ERROR,
                  "fmi3%s rejects a non-empty request" % name)
            if logging:
                check(len(messages) == 1 and messages[0][3] == ABSENT_MESSAGE,
                      "fmi3%s logs the absent-type message once" % name)
            else:
                check(messages == [], "fmi3%s non-empty request suppressed" % name)
            free(handle)

    # -- lifecycle-illegal calls (representative of the proved rejection class) --
    handle = cs(True)
    get_deriv = fn("GetContinuousStateDerivatives", [P, C.POINTER(D), N])
    enter_ctm = fn("EnterContinuousTimeMode", [P])
    scratch = (D * 8)()
    messages.clear()
    check(do_step(handle, 0.0, 1.0) == ERROR, "fmi3DoStep before initialization is rejected")
    check(get_deriv(handle, scratch, n_states) == ERROR,
          "fmi3GetContinuousStateDerivatives in a co-simulation instance is rejected")
    check(messages and messages[-1][3] == LIFECYCLE_MESSAGE,
          "the co-simulation derivative rejection logs the lifecycle message")
    check(set_time(handle, 1.0) == ERROR, "fmi3SetTime in a co-simulation instance is rejected")
    check(enter_ctm(handle) == ERROR,
          "fmi3EnterContinuousTimeMode in a co-simulation instance is rejected")
    check(terminate(handle) == ERROR, "fmi3Terminate before initialization is rejected")
    free(handle)

    # -- argument rejection: non-finite set value, unknown reference, wrong nValues --
    handle = cs(False)
    check(enter_init(handle, False, 0.0, 0.0, False, 0.0) == OK, "argument fixture initialization")
    non_finite = (D * cfg["input_n"])(*([math.nan] * cfg["input_n"]))
    check(set_f64(handle, (VR * 1)(cfg["input_vr"]), 1, non_finite, cfg["input_n"]) == ERROR,
          "fmi3SetFloat64 rejects a non-finite value")
    check(get_f64(handle, (VR * 1)(9999), 1, scratch, 1) == ERROR,
          "fmi3GetFloat64 rejects an unknown value reference")
    check(get_f64(handle, (VR * 1)(cfg["get_vr"]), 1, scratch, cfg["get_n"] + 1) == ERROR,
          "fmi3GetFloat64 rejects a mismatched nValues")
    free(handle)

    # -- communication-step discard for an off-grid step, then an on-grid success --
    handle = cs(False)
    check(initialize(handle), "discard fixture initialization")
    check(do_step(handle, 0.0, 0.5) == DISCARD, "fmi3DoStep discards an off-grid step")
    check(do_step(handle, 0.0, 1.0) == OK, "fmi3DoStep accepts an on-grid step")
    free(handle)

    # -- fmi3Reset followed by re-initialization --
    handle = cs(False)
    check(initialize(handle), "reset fixture initialization")
    check(reset(handle) == OK, "fmi3Reset returns fmi3OK")
    check(initialize(handle), "re-initialization after reset")
    check(do_step(handle, 0.0, 1.0) == OK, "a step after reset and re-initialization succeeds")
    free(handle)

    # -- fmi3SetDebugLogging with valid and invalid category lists --
    handle = cs(True)
    set_logging = fn("SetDebugLogging", [P, B, N, C.POINTER(C.c_char_p)])
    messages.clear()
    check(set_logging(handle, True, 1, (C.c_char_p * 1)(b"logStatus")) == OK,
          "fmi3SetDebugLogging accepts a known category")
    check(set_logging(handle, False, 0, None) == OK, "fmi3SetDebugLogging accepts an empty disable")
    messages.clear()
    check(set_logging(handle, True, 1, (C.c_char_p * 1)(b"unknown")) == ERROR,
          "fmi3SetDebugLogging rejects an unknown category")
    messages.clear()
    check(set_logging(handle, True, 1, None) == ERROR,
          "fmi3SetDebugLogging rejects a missing category list")
    free(handle)

    # -- model-facing suppressed versus enabled logging split --
    quiet, loud = cs(False), cs(True)
    messages.clear()
    check(terminate(quiet) == ERROR and messages == [],
          "a rejected fmi3Terminate emits no callback with logging off")
    messages.clear()
    check(terminate(loud) == ERROR and len(messages) == 1
          and messages[0][:3] == (123, ERROR, b"logStatus"),
          "a rejected fmi3Terminate emits one callback with logging on")
    free(quiet)
    free(loud)

    # -- co-simulation success path --
    handle = cs(False)
    check(enter_init(handle, False, 0.0, 0.0, False, 0.0) == OK, "co-simulation EnterInitializationMode")
    check(set_f64(handle, (VR * 1)(cfg["input_vr"]), 1,
                  (D * cfg["input_n"])(*cfg["start"]), cfg["input_n"]) == OK,
          "co-simulation SetFloat64 success")
    check(exit_init(handle) == OK, "co-simulation ExitInitializationMode")
    check(do_step(handle, 0.0, 1.0) == OK, "co-simulation DoStep success")
    check(get_f64(handle, (VR * 1)(cfg["get_vr"]), 1, scratch, cfg["get_n"]) == OK,
          "co-simulation GetFloat64 success")
    check(terminate(handle) == OK, "co-simulation Terminate success")
    free(handle)

    # -- model-exchange success path (covers the remaining model-facing functions) --
    handle = me(False)
    count = N(0)
    get_ncs = fn("GetNumberOfContinuousStates", [P, C.POINTER(N)])
    get_nei = fn("GetNumberOfEventIndicators", [P, C.POINTER(N)])
    get_states = fn("GetContinuousStates", [P, C.POINTER(D), N])
    set_states = fn("SetContinuousStates", [P, C.POINTER(D), N])
    get_nominals = fn("GetNominalsOfContinuousStates", [P, C.POINTER(D), N])
    get_indicators = fn("GetEventIndicators", [P, C.POINTER(D), N])
    evaluate = fn("EvaluateDiscreteStates", [P])
    update = fn("UpdateDiscreteStates", [P] + [C.POINTER(B)] * 5 + [C.POINTER(D)])
    completed = fn("CompletedIntegratorStep", [P, B, C.POINTER(B), C.POINTER(B)])
    enter_event = fn("EnterEventMode", [P])
    check(get_ncs(handle, C.byref(count)) == OK and count.value == n_states,
          "model-exchange GetNumberOfContinuousStates success")
    check(get_nei(handle, C.byref(count)) == OK, "model-exchange GetNumberOfEventIndicators success")
    check(enter_init(handle, False, 0.0, 0.0, False, 0.0) == OK, "model-exchange EnterInitializationMode")
    buffer = (D * n_states)()
    check(get_states(handle, buffer, n_states) == OK, "model-exchange GetContinuousStates success")
    check(get_deriv(handle, buffer, n_states) == OK, "model-exchange GetContinuousStateDerivatives success")
    check(get_nominals(handle, buffer, n_states) == OK, "model-exchange GetNominalsOfContinuousStates success")
    check(get_indicators(handle, None, 0) == OK, "model-exchange GetEventIndicators success")
    check(exit_init(handle) == OK, "model-exchange ExitInitializationMode")
    check(evaluate(handle) == OK, "model-exchange EvaluateDiscreteStates success")
    flags = [B() for _ in range(5)]
    next_time = D()
    check(update(handle, *map(C.byref, flags), C.byref(next_time)) == OK,
          "model-exchange UpdateDiscreteStates success")
    check(enter_ctm(handle) == OK, "model-exchange EnterContinuousTimeMode success")
    check(set_time(handle, 1.0) == OK, "model-exchange SetTime success")
    check(set_states(handle, (D * n_states)(*([0.5] * n_states)), n_states) == OK,
          "model-exchange SetContinuousStates success")
    event, terminated = B(), B()
    check(completed(handle, True, C.byref(event), C.byref(terminated)) == OK,
          "model-exchange CompletedIntegratorStep success")
    check(enter_event(handle) == OK, "model-exchange EnterEventMode success")
    check(terminate(handle) == OK, "model-exchange Terminate success")
    free(handle)

    return len(funcs), cells[0], discrepancies


if len(sys.argv) >= 3 and sys.argv[1] == "--matrix":
    matrix_fmu = Path(sys.argv[2]).resolve()
    matrix_label = sys.argv[3] if len(sys.argv) > 3 else matrix_fmu.stem
    touched, exercised, differences = behavior_matrix(matrix_fmu, matrix_label)
    known = KNOWN_DISCREPANCIES.get(matrix_label, set())
    unexpected = [d for d in differences if d not in known]
    for difference in differences:
        tag = "recorded finding" if difference in known else "REGRESSION"
        print("DISCREPANCY [%s] (%s) %s" % (matrix_label, tag, difference))
    print("MATRIX %s: %d/75 functions, %d behavior cells exercised, "
          "%d recorded-finding discrepancies, %d unexpected"
          % (matrix_label, touched, exercised, len(differences) - len(unexpected), len(unexpected)))
    if unexpected or touched != 75:
        sys.exit(1)
    sys.exit(0)


FMU = Path(sys.argv.pop(1)).resolve()
PEER_FMU = Path(sys.argv.pop(1)).resolve()
VENDOR = Path(__file__).resolve().parents[1] / "packages/backend-fmi3/vendor/fmi3"


class FMI3Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="rumoca-fmi-test-")
        cls.root = Path(cls.tmp.name)
        with zipfile.ZipFile(FMU) as archive:
            for entry in archive.infolist():
                path = PurePosixPath(entry.filename)
                if path.is_absolute() or ".." in path.parts or "\\" in entry.filename:
                    raise ValueError("unsafe FMU member")
            archive.extractall(cls.root)
        cls.md = read_model_description(FMU, validate=True)
        cls.state = next(v.name for v in cls.md.modelVariables if v.valueReference == 1)
        cls.library = next((cls.root / "binaries").glob("*-linux/*.so"))
        cls.dll = C.CDLL(str(cls.library))

        def bind(name, args, result=C.c_int):
            fn = getattr(cls.dll, "fmi3" + name)
            fn.argtypes = args
            fn.restype = result
            setattr(cls, name, staticmethod(fn))

        bind("GetVersion", [], C.c_char_p)
        bind("InstantiateModelExchange", [C.c_char_p, C.c_char_p, C.c_char_p, B, B, P, LOG], P)
        bind("InstantiateCoSimulation", [C.c_char_p, C.c_char_p, C.c_char_p, B, B, B, B,
                                          C.POINTER(VR), N, P, LOG, P], P)
        bind("FreeInstance", [P], None)
        bind("EnterInitializationMode", [P, B, D, D, B, D])
        for name in ["ExitInitializationMode", "EnterEventMode", "EnterContinuousTimeMode",
                     "EvaluateDiscreteStates", "Terminate", "Reset"]:
            bind(name, [P])
        for name in ["GetFloat64", "SetFloat64"]:
            bind(name, [P, C.POINTER(VR), N, C.POINTER(D), N])
        bind("SetTime", [P, D])
        for name in ["GetContinuousStates", "GetContinuousStateDerivatives",
                     "SetContinuousStates", "GetNominalsOfContinuousStates", "GetEventIndicators"]:
            bind(name, [P, C.POINTER(D), N])
        for name in ["GetNumberOfContinuousStates", "GetNumberOfEventIndicators"]:
            bind(name, [P, C.POINTER(N)])
        bind("UpdateDiscreteStates", [P] + [C.POINTER(B)] * 5 + [C.POINTER(D)])
        bind("CompletedIntegratorStep", [P, B, C.POINTER(B), C.POINTER(B)])
        bind("DoStep", [P, D, D, B] + [C.POINTER(B)] * 3 + [C.POINTER(D)])
        bind("GetInt32", [P, C.POINTER(VR), N, C.POINTER(C.c_int32), N])
        bind("SetInt32", [P, C.POINTER(VR), N, C.POINTER(C.c_int32), N])
        bind("SetDebugLogging", [P, B, N, C.POINTER(C.c_char_p)])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def setUp(self):
        self.handles = []
        self.messages = []
        self.logger = LOG(lambda env, status, category, message:
                          self.messages.append((env, status, category, message)))

    def tearDown(self):
        for handle in self.handles:
            self.FreeInstance(handle)

    def create(self, kind="cs", token=None, name=b"test", logging=False, events=False):
        token = self.md.instantiationToken.encode() if token is None else token
        args = [name, token, None, False, logging]
        if kind == "cs":
            handle = self.InstantiateCoSimulation(*args, events, False, None, 0, P(123), self.logger, None)
        else:
            handle = self.InstantiateModelExchange(*args, P(123), self.logger)
        if handle:
            self.handles.append(handle)
        return handle

    def initialize(self, handle, kind="cs", start=0.5, time=0.0, stop=None):
        self.assertEqual(self.SetFloat64(handle, (VR * 1)(1), 1, (D * 1)(start), 1), OK)
        self.assertEqual(self.EnterInitializationMode(handle, False, 0, time, stop is not None,
                                                    stop if stop is not None else 0), OK)
        self.assertEqual(self.ExitInitializationMode(handle), OK)
        if kind == "me":
            flags = [B(True) for _ in range(5)]
            next_time = D(-1)
            self.assertEqual(self.UpdateDiscreteStates(handle, *map(C.byref, flags), C.byref(next_time)), OK)
            self.assertFalse(any(f.value for f in flags))
            self.assertEqual(self.EnterContinuousTimeMode(handle), OK)

    def values(self, handle):
        values = (D * 3)()
        self.assertEqual(self.GetFloat64(handle, (VR * 3)(0, 1, 2), 3, values, 3), OK)
        return tuple(values)

    def step(self, handle, time, size):
        flags = [B(True) for _ in range(3)]
        last = D(-99)
        status = self.DoStep(handle, time, size, True, *map(C.byref, flags), C.byref(last))
        return status, tuple(f.value for f in flags), last.value

    def test_archive_and_schema(self):
        self.assertEqual(validate_fmu(FMU), [])
        self.assertEqual(self.md.fmiVersion, "3.0")
        self.assertIsNotNone(self.md.modelExchange)
        self.assertIsNotNone(self.md.coSimulation)
        self.assertEqual(float(self.md.coSimulation.fixedInternalStepSize), 1)
        self.assertEqual(self.GetVersion(), b"3.0")
        with zipfile.ZipFile(FMU) as archive:
            names = archive.namelist()
            self.assertEqual(len(names), len(set(names)))
            for entry in archive.infolist():
                self.assertIn(entry.compress_type, [0, 8])
                self.assertLessEqual(entry.extract_version, 20)
                self.assertFalse(entry.flag_bits & 1)
                self.assertNotEqual((entry.external_attr >> 16) & 0o170000, 0o120000)
            self.assertIn("modelDescription.xml", names)
            self.assertIn("sources/buildDescription.xml", names)
            self.assertIn("extra/org.cognipilot.rumoca/kernel-audit.log", names)
            self.assertFalse(any(name.endswith(".h") for name in names))
        # Every entry point mandated by the pinned public header must be present.
        required = re.findall(r"FMI3_Export\s+\w+TYPE\s+(fmi3\w+)\s*;",
                              (VENDOR / "fmi3Functions.h").read_text())
        self.assertGreater(len(required), 70)
        for name in required:
            self.assertTrue(hasattr(self.dll, name), name)

    def test_both_importer_traces(self):
        for interface in ["ModelExchange", "CoSimulation"]:
            result = simulate_fmu(FMU, validate=True, fmi_type=interface, solver="Euler",
                                  start_time=0, stop_time=3, step_size=1, output_interval=1,
                                  start_values={self.state: 0.5}, output=[self.state], record_events=False)
            self.assertEqual(list(result["time"]), [0, 1, 2, 3])
            self.assertEqual(list(result[self.state]), [0.5, 1.5, 2.5, 3.5])

    def test_bad_instantiation_and_logging(self):
        for name in [b"", b" \t\r\n", None]:
            self.assertFalse(self.create(name=name))
        self.assertFalse(self.create(token=b"wrong"))
        self.assertFalse(self.create(token=None, events=True))
        self.assertEqual(self.messages, [])
        self.assertFalse(self.create(token=b"wrong", logging=True))
        self.assertEqual(self.messages[-1][:3], (123, ERROR, b"logStatus"))
        h = self.create(logging=True)
        self.assertEqual(self.SetDebugLogging(h, False, 0, None), OK)
        self.messages.clear()
        self.assertEqual(self.Terminate(h), ERROR)
        self.assertEqual(self.messages, [])
        # Exercise the native string-array ABI used by the proved validation
        # loop. Universal behavior and memory frames are checked in Lean.
        valid = (C.c_char_p * 3)(b"logStatus", b"logStatus", b"logStatus")
        for kind in ["me", "cs"]:
            h = self.create(kind)
            initial = self.values(h)
            self.assertEqual(self.SetDebugLogging(h, True, 3, valid), OK)
            self.assertEqual(self.SetDebugLogging(h, False, 3, valid), OK)
            self.assertEqual(self.SetDebugLogging(h, True, 0, None), OK)
            self.assertEqual(self.values(h), initial)
            self.messages.clear()
            self.assertEqual(self.Terminate(h), ERROR)
            self.assertEqual(len(self.messages), 1)
            self.assertEqual(self.messages[0][:3], (123, ERROR, b"logStatus"))
            for categories, count, message in [
                (None, 1, b"Missing log categories"),
                ((C.c_char_p * 2)(b"logStatus", None), 2, b"Unknown log category"),
                ((C.c_char_p * 2)(b"logStatus", b"unknown"), 2, b"Unknown log category"),
            ]:
                for old_logging in [False, True]:
                    h = self.create(kind, logging=old_logging)
                    self.messages.clear()
                    self.assertEqual(self.SetDebugLogging(h, not old_logging, count, categories), ERROR)
                    # Rejection uses the original policy: a valid prefix must
                    # not change the flag before all categories are accepted.
                    self.assertEqual(self.messages, [(123, ERROR, b"logStatus", message)] if old_logging else [])
        self.messages.clear()
        self.assertEqual(self.SetDebugLogging(None, True, 1, None), ERROR)
        self.assertEqual(self.messages, [])
        self.FreeInstance(None)

    def test_lifecycle_reset_and_isolation(self):
        a, b = self.create(), self.create()
        self.initialize(a, start=-3)
        self.initialize(b, start=4)
        self.assertEqual(self.step(a, 0, 2), (OK, (False, False, False), 2))
        self.assertEqual(self.values(a), (2, -1, 1))
        self.assertEqual(self.values(b), (0, 4, 1))
        self.assertEqual(self.SetTime(a, 2), ERROR)  # ME entry point on CS
        # FMI 3.0.2 §2.3.8: final values remain readable after fmi3Error.
        self.assertEqual(self.GetFloat64(a, None, 0, None, 0), OK)
        self.assertEqual(self.values(a), (2, -1, 1))
        self.assertEqual(self.values(b), (0, 4, 1))
        self.assertEqual(self.step(a, 2, 1)[0], ERROR)
        self.assertEqual(self.values(a), (2, -1, 1))
        self.assertEqual(self.Reset(a), OK)
        self.assertEqual(self.values(a), (0, 0, 1))
        self.initialize(a)
        self.assertEqual(self.Terminate(a), OK)
        self.assertEqual(self.step(a, 0, 1)[0], ERROR)
        self.assertEqual(self.Reset(a), OK)
        self.assertEqual(self.step(a, 0, 1)[0], ERROR)  # before initialization

        # Native boundary for the proved static-storage replacement: ME and CS
        # share capacity, exhaustion preserves live instances, and reuse starts
        # with fresh state/lifecycle fields. The Lean contracts quantify over
        # storage and calls; this checks the compiled object layout and ABI.
        for handle in self.handles:
            self.FreeInstance(handle)
        self.handles.clear()
        declaration = re.search(r"static const size_t rumoca_instance_capacity = (\d+);",
                                (self.root / "sources/fmi3.c").read_text())
        self.assertIsNotNone(declaration)
        capacity = int(declaration[1])
        self.assertEqual(capacity, 32)  # Current deployment profile.
        for index in range(capacity):
            kind = "me" if index % 2 == 0 else "cs"
            handle = self.create(kind)
            self.assertTrue(handle)
            self.initialize(handle, kind, start=index + 0.5, stop=10)
        self.assertEqual(len(set(self.handles)), capacity)
        self.assertFalse(self.create("me", logging=True))
        self.assertFalse(self.create("cs", logging=True))
        self.assertEqual(self.messages[-1][:3], (123, ERROR, b"logStatus"))
        for index, handle in enumerate(self.handles):
            self.assertEqual(self.values(handle), (0, index + 0.5, 1))
        self.FreeInstance(self.handles.pop(0))
        reused = self.create("cs")
        self.assertTrue(reused)
        self.assertEqual(self.values(reused), (0, 0, 1))
        self.initialize(reused, stop=None)
        self.assertEqual(self.step(reused, 0, 11), (OK, (False, False, False), 11))
        self.assertFalse(self.create("me"))

    def test_me_initialization_event_and_state_access(self):
        # FMI 3.0.2 §2.3.2 excludes nominals in Instantiated. Rejection must
        # preserve the caller's output, enter Terminated, and respect loggingOn.
        for logging in [False, True]:
            rejected = self.create("me", logging=logging)
            nominal = (D * 1)(42)
            before = len(self.messages)
            self.assertEqual(self.GetNominalsOfContinuousStates(rejected, nominal, 1), ERROR)
            self.assertEqual(nominal[0], 42)
            expected = [(123, ERROR, b"logStatus", b"Call is not allowed in the current FMI state")] if logging else []
            self.assertEqual(self.messages[before:], expected)
            # The same query is available for final observations in Terminated.
            self.assertEqual(self.GetNominalsOfContinuousStates(rejected, nominal, 1), OK)
            self.assertEqual(nominal[0], 1)
            self.assertEqual(self.Reset(rejected), OK)
            self.assertEqual(self.EnterInitializationMode(rejected, False, 0, 0, False, 0), OK)
            self.assertEqual(self.GetNominalsOfContinuousStates(rejected, nominal, 1), OK)
            # Evaluation is event-only; exercise the corrected native guard.
            values = self.values(rejected)
            before = len(self.messages)
            self.assertEqual(self.EvaluateDiscreteStates(rejected), ERROR)
            self.assertEqual(self.messages[before:], expected)
            self.assertEqual(self.values(rejected), values)
        h = self.create("me")
        count = N(99)
        self.assertEqual(self.GetNumberOfContinuousStates(h, C.byref(count)), OK)
        self.assertEqual(count.value, 1)
        self.assertEqual(self.GetNumberOfEventIndicators(h, C.byref(count)), OK)
        self.assertEqual(count.value, 0)
        self.assertEqual(self.EnterInitializationMode(h, False, 0, 0, False, 0), OK)
        out = (D * 1)()
        for method in [self.GetContinuousStates, self.GetContinuousStateDerivatives,
                       self.GetNominalsOfContinuousStates]:
            self.assertEqual(method(h, out, 1), OK)
        self.assertEqual(self.GetEventIndicators(h, None, 0), OK)
        self.assertEqual(self.ExitInitializationMode(h), OK)
        self.assertEqual(self.GetNumberOfContinuousStates(h, C.byref(count)), OK)
        self.assertEqual(count.value, 1)
        self.assertEqual(self.GetNumberOfEventIndicators(h, C.byref(count)), OK)
        self.assertEqual(count.value, 0)
        self.assertEqual(self.GetContinuousStateDerivatives(h, out, 1), OK)
        self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, (D * 1)(2), 1), OK)
        # The omitted capability has a false default: evaluation is a no-op.
        values = self.values(h)
        self.assertEqual(self.EvaluateDiscreteStates(h), OK)
        self.assertEqual(self.values(h), values)
        flags, next_time = [B() for _ in range(5)], D()
        self.assertEqual(self.UpdateDiscreteStates(h, *map(C.byref, flags), C.byref(next_time)), OK)
        self.assertEqual(self.EnterContinuousTimeMode(h), OK)
        self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, (D * 1)(4), 1), OK)
        self.assertEqual(self.SetContinuousStates(h, (D * 1)(7), 1), OK)
        self.assertEqual(self.values(h), (0, 7, 1))
        self.assertEqual(self.Terminate(h), OK)
        final = (D * 1)()
        for getter, expected in [(self.GetContinuousStates, 7),
                                 (self.GetContinuousStateDerivatives, 1),
                                 (self.GetNominalsOfContinuousStates, 1)]:
            self.assertEqual(getter(h, final, 1), OK)
            self.assertEqual(final[0], expected)
        self.assertEqual(self.GetEventIndicators(h, None, 0), OK)
        count.value = 99
        self.assertEqual(self.GetNumberOfContinuousStates(h, C.byref(count)), ERROR)
        self.assertEqual(count.value, 99)
        self.assertEqual(self.SetTime(h, 1), ERROR)
        self.assertEqual(self.GetContinuousStates(h, final, 1), OK)
        self.assertEqual(final[0], 7)

    def test_me_time_backtracking_and_stop(self):
        h = self.create("me")
        self.initialize(h, "me", stop=5)
        event, terminate = B(), B()
        for time in [1, 2]:
            self.assertEqual(self.SetTime(h, time), OK)
            self.assertEqual(self.CompletedIntegratorStep(h, True, C.byref(event), C.byref(terminate)), OK)
        self.assertEqual(self.SetTime(h, 1), OK)  # second-last completed time
        self.assertEqual(self.SetTime(h, 0.5), ERROR)
        self.assertEqual(self.Reset(h), OK)
        self.initialize(h, "me", stop=5)
        self.assertEqual(self.SetTime(h, 2), OK)
        self.assertEqual(self.EnterEventMode(h), OK)
        flags, next_time = [B() for _ in range(5)], D()
        self.assertEqual(self.UpdateDiscreteStates(h, *map(C.byref, flags), C.byref(next_time)), OK)
        self.assertEqual(self.EnterContinuousTimeMode(h), OK)
        self.assertEqual(self.SetTime(h, 1.5), ERROR)
        self.assertEqual(self.Reset(h), OK)
        self.initialize(h, "me", stop=5)
        self.assertEqual(self.SetTime(h, 6), ERROR)

    def test_me_history_drops_obsolete_completion(self):
        h = self.create("me")
        for origin in [0.0, -4.0]:
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h, "me", time=origin)
            event, terminate = B(True), B(True)
            # Every SetTime is admitted by the positional history bounds.
            # A running maximum incorrectly retains origin + 2 at the end.
            for offset in [1.0, 2.0, 1.0, 2.0]:
                self.assertEqual(self.SetTime(h, origin + offset), OK)
                self.assertEqual(self.SetContinuousStates(h, (D * 1)(0.5 + offset), 1), OK)
                self.assertEqual(self.CompletedIntegratorStep(h, True, C.byref(event), C.byref(terminate)), OK)
                self.assertFalse(event.value)
                self.assertFalse(terminate.value)
            self.assertEqual(self.SetTime(h, origin + 1.5), OK)
            self.assertEqual(self.SetContinuousStates(h, (D * 1)(2.0), 1), OK)
            self.assertEqual(self.EnterEventMode(h), OK)
            flags, next_time = [B() for _ in range(5)], D()
            self.assertEqual(self.UpdateDiscreteStates(h, *map(C.byref, flags), C.byref(next_time)), OK)
            self.assertEqual(self.EnterContinuousTimeMode(h), OK)
            self.assertEqual(self.SetTime(h, origin + 1.5), OK)
            self.assertEqual(self.SetTime(h, origin + 1.0), ERROR)  # retained event floor

    def test_me_history_public_outputs(self):
        h, other = self.create("me"), self.create("me")
        self.initialize(h, "me", start=-0.0)
        self.initialize(other, "me", start=123.5)
        self.assertEqual(self.SetTime(h, 0.5), OK)
        aliased = B(True)
        self.assertEqual(self.CompletedIntegratorStep(h, False, C.byref(aliased), C.byref(aliased)), OK)
        self.assertFalse(aliased.value)
        self.assertEqual(self.EnterEventMode(h), OK)
        self.assertEqual(self.values(h), (0.5, -0.0, 1.0))
        self.assertEqual(struct.pack("d", self.values(h)[1]), struct.pack("d", -0.0))
        self.assertEqual(self.values(other), (0.0, 123.5, 1.0))
        flags, next_time = [B() for _ in range(5)], D()
        self.assertEqual(self.UpdateDiscreteStates(h, *map(C.byref, flags), C.byref(next_time)), OK)
        self.assertEqual(self.EnterContinuousTimeMode(h), OK)
        event, terminate = B(True), B(True)
        self.assertEqual(self.CompletedIntegratorStep(h, True, C.byref(event), C.byref(terminate)), OK)
        self.assertFalse(event.value)
        self.assertFalse(terminate.value)
        self.assertEqual(struct.pack("d", self.values(h)[1]), struct.pack("d", -0.0))

    def test_me_time_binary64_bounds(self):
        h = self.create("me")
        tiny = math.ulp(0.0)
        for origin, stop, times in [
            (0.0, None, [-0.0, 0.0, tiny, -0.0]),
            (-tiny, None, [-tiny, -0.0, tiny]),
            (0.5, 1.5, [1.0, 0.5, 1.5]),
            (-sys.float_info.max, None, [sys.float_info.max, -sys.float_info.max]),
        ]:
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h, "me", start=-0.0, time=origin, stop=stop)
            for time in times:
                self.assertEqual(self.SetTime(h, time), OK)
                actual_time, state, derivative = self.values(h)
                self.assertEqual(struct.pack("d", actual_time), struct.pack("d", time))
                self.assertEqual(struct.pack("d", state), struct.pack("d", -0.0))
                self.assertEqual(derivative, 1.0)
        signaling_nan = struct.unpack("d", struct.pack("Q", 0x7ff0000000000001))[0]
        for invalid in [-tiny, math.nextafter(1.5, math.inf), math.nan, signaling_nan, math.inf, -math.inf]:
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h, "me", stop=1.5)
            self.assertEqual(self.SetTime(h, invalid), ERROR)

    def test_discard_is_atomic_and_retryable(self):
        h = self.create()
        self.initialize(h)
        for size in [0.5, 1.5, 1000001]:
            self.assertEqual(self.step(h, 0, size), (DISCARD, (False, False, False), 0))
            self.assertEqual(self.values(h), (0, 0.5, 1))
        self.assertEqual(self.step(h, 0, 1)[0], OK)
        self.assertEqual(self.Reset(h), OK)
        self.initialize(h, time=2**53)
        self.assertEqual(self.step(h, 2**53, 1), (DISCARD, (False, False, False), 2**53))
        self.assertEqual(self.values(h)[1], 0.5)
        # Native overflow boundary: the existing C adds before rejecting the
        # unsupported increment. Retain the stop-error/discard precedence.
        maximum = sys.float_info.max
        for stop, status in [(None, DISCARD), (maximum, ERROR)]:
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h, time=maximum, stop=stop)
            self.assertEqual(self.step(h, maximum, maximum),
                             (status, (False, False, False), maximum))
            self.assertEqual(self.values(h), (maximum, 0.5, 1))

    def test_invalid_arguments_and_output_atomicity(self):
        # Native ABI boundary for the proved unit-profile initialization policy.
        self.assertEqual(self.EnterInitializationMode(None, True, math.nan, math.nan, True, math.nan), ERROR)
        for kind in ["me", "cs"]:
            initialized = self.create(kind, logging=True)
            for arguments in [(True, 0.0, 2.0, True, 2.0),
                              (True, math.nan, -0.0, False, math.nan)]:
                self.assertEqual(self.Reset(initialized), OK)
                self.assertEqual(self.SetFloat64(initialized, (VR * 1)(1), 1, (D * 1)(-0.0), 1), OK)
                self.assertEqual(self.EnterInitializationMode(initialized, *arguments), OK)
                self.assertEqual(self.ExitInitializationMode(initialized), OK)
                time, state, derivative = self.values(initialized)
                self.assertEqual(struct.pack("d", time), struct.pack("d", arguments[2]))
                self.assertEqual(struct.pack("d", state), struct.pack("d", -0.0))
                self.assertEqual(derivative, 1.0)
            for start, defined, stop in [(math.nan, False, 0.0), (math.inf, False, 0.0),
                                         (2.0, True, 1.0), (0.0, True, math.nan)]:
                self.assertEqual(self.Reset(initialized), OK)
                before = len(self.messages)
                self.assertEqual(self.EnterInitializationMode(initialized, False, 0.0, start, defined, stop), ERROR)
                self.assertEqual(self.messages[before:],
                                 [(123, ERROR, b"logStatus", b"Invalid initialization time interval")])
                self.assertEqual(self.values(initialized), (0.0, 0.0, 1.0))
                self.assertEqual(self.ExitInitializationMode(initialized), ERROR)
        self.assertEqual(self.SetFloat64(None, None, 0, None, 0), ERROR)
        self.assertEqual(self.SetFloat64(None, None, 1, None, 1), ERROR)
        h = self.create()
        for value in [math.nan, math.inf, -math.inf]:
            self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, (D * 1)(value), 1), ERROR)
            self.assertEqual(self.Reset(h), OK)
        out = (D * 2)(99, 99)
        self.assertEqual(self.GetFloat64(h, (VR * 2)(1, 99), 2, out, 2), ERROR)
        self.assertEqual(list(out), [99, 99])
        self.assertEqual(self.Reset(h), OK)
        self.assertEqual(self.GetFloat64(h, None, 1, out, 1), ERROR)
        self.assertEqual(self.Reset(h), OK)
        self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, out, 2), ERROR)
        self.assertEqual(self.Reset(h), OK)
        self.initialize(h)
        self.assertEqual(self.GetFloat64(h, None, 0, None, 0), OK)
        unchanged = self.values(h)
        self.assertEqual(self.SetFloat64(h, None, 0, None, 0), OK)
        self.assertEqual(self.values(h), unchanged)
        self.assertEqual(self.GetInt32(h, None, 0, None, 0), OK)
        self.assertEqual(self.SetInt32(h, None, 0, None, 0), OK)
        for point, size in [(1, 1), (0, 0), (0, -1), (math.nan, 1), (0, math.inf)]:
            self.assertEqual(self.step(h, point, size)[0], ERROR)
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h)
        self.assertEqual(self.DoStep(h, 0, 1, True, None, None, None, None), ERROR)
        self.assertEqual(self.Reset(h), OK)
        self.initialize(h, stop=1)
        self.assertEqual(self.step(h, 0, 2)[0], ERROR)

        # Exercise the native ABI and logger transport for the formally
        # classified empty-setter rejection; both interfaces use the same guard.
        for kind in ["cs", "me"]:
            terminated = self.create(kind, logging=True)
            self.initialize(terminated, kind)
            before_values = self.values(terminated)
            self.assertEqual(self.Terminate(terminated), OK)
            references = (VR * 1)(1)
            for setter, unused in [(self.SetFloat64, (D * 1)(99)),
                                   (self.SetInt32, (C.c_int32 * 1)(99))]:
                before_messages = len(self.messages)
                self.assertEqual(setter(terminated, references, 0, unused, 0), ERROR)
                self.assertEqual(self.messages[before_messages:],
                                 [(123, ERROR, b"logStatus", b"Call is not allowed in the current FMI state")])
                self.assertEqual(self.values(terminated), before_values)
            self.assertEqual(self.GetFloat64(terminated, references, 0, (D * 1)(99), 0), OK)

    def test_binary64_kernel_through_cs(self):
        h = self.create()
        starts = [-0.0, 0.0, -0.5, -2, 0.5, 2**53, -(2**53),
                  math.ulp(0.0), -math.ulp(0.0), sys.float_info.max, -sys.float_info.max]
        for start in starts:
            self.assertEqual(self.Reset(h), OK)
            self.initialize(h, start=start)
            expected = start
            for _ in range(3):
                expected += 1.0
            self.assertEqual(self.step(h, 0, 3)[0], OK)
            self.assertEqual(struct.pack("d", self.values(h)[1]), struct.pack("d", expected))

    def test_sources_rebuild_without_lean(self):
        # Validate the published schema, then use its actual compiler, flags,
        # source names and dependencies. The importer supplies only FMI headers
        # and the shared-object output convention for the selected Linux host.
        def recipe(root):
            read_build_description(root, validate=True)
            md = read_model_description(root, validate=True)
            identifier = md.modelExchange.modelIdentifier
            self.assertEqual(identifier, md.coSimulation.modelIdentifier)
            build = ElementTree.parse(root / "sources/buildDescription.xml")
            configs = [c for c in build.findall("BuildConfiguration")
                       if c.get("modelIdentifier") == identifier
                       and c.get("platform") == self.library.parent.name]
            self.assertEqual(len(configs), 1)
            sets = configs[0].findall("SourceFileSet")
            self.assertEqual(len(sets), 1)
            source_set = sets[0]
            self.assertEqual(source_set.get("language"), "C11")
            sources = [str(root / "sources" / s.get("name"))
                       for s in source_set.findall("SourceFile")]
            libraries = configs[0].findall("Library")
            self.assertTrue(all(lib.get("external") == "true" for lib in libraries))
            return (identifier, source_set.get("compiler"),
                    shlex.split(source_set.get("compilerOptions", "")), sources,
                    ["-l" + lib.get("name") for lib in libraries])

        identifier, compiler, options, sources, libraries = recipe(self.root)
        rebuilt = self.root / "rebuilt.so"
        subprocess.run([compiler, *options, "-fPIC", "-shared",
                        "-DFMI3_OVERRIDE_FUNCTION_PREFIX", "-I", str(VENDOR), *sources, *libraries,
                        "-o", str(rebuilt)], check=True)
        # Check actual host linkage as well as the source-level contracts. This
        # does not certify the internals of libc or user-supplied callbacks.
        for binary in (self.library, rebuilt):
            undefined = subprocess.check_output(["nm", "-u", str(binary)], text=True)
            symbols = {line.split()[-1].split("@")[0] for line in undefined.splitlines()}
            self.assertFalse(symbols & {"malloc", "calloc", "realloc", "free", "aligned_alloc"})
            self.assertFalse(any(symbol.startswith("__atomic_") for symbol in symbols))
        # Python already loads libm and can hide a missing dependency. Resolve
        # every symbol in a fresh loader process which links only libdl.
        loader_source = self.root / "load.c"
        loader_source.write_text('''#include <dlfcn.h>
#include <stdio.h>
int main(int argc, char **argv) {
  if (argc != 2) return 2;
  void *library = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  if (!library) { fprintf(stderr, "%s\\n", dlerror()); return 1; }
  return dlclose(library) != 0;
}
''')
        loader = self.root / "load"
        subprocess.run(["gcc", str(loader_source), "-ldl", "-o", str(loader)], check=True)
        subprocess.run([str(loader), str(rebuilt)], check=True)
        library = C.CDLL(str(rebuilt))
        fn = library.fmi3GetVersion
        fn.argtypes, fn.restype = [], C.c_char_p
        self.assertEqual(fn(), b"3.0")

        # Static source composition uses the prefixes declared by the FMUs,
        # without caller-invented names or exposed numerical helpers.
        peer = self.root / "peer"
        with zipfile.ZipFile(PEER_FMU) as archive:
            archive.extractall(peer)
        recipes = [recipe(self.root), recipe(peer)]
        self.assertNotEqual(recipes[0][0], recipes[1][0])
        objects = []
        dependencies = []
        for index, (_, cc, flags, files, libs) in enumerate(recipes):
            self.assertEqual(len(files), 1)
            obj = self.root / f"source-{index}.o"
            subprocess.run([cc, *flags, "-fPIC", "-I", str(VENDOR), "-c", files[0], "-o", str(obj)], check=True)
            objects.append(str(obj))
            dependencies.extend(libs)
        combined = self.root / "combined.so"
        subprocess.run([compiler, "-shared", *objects, *dependencies, "-o", str(combined)], check=True)
        subprocess.run([str(loader), str(combined)], check=True)
        exports = subprocess.check_output(["nm", "-g", "--defined-only", str(combined)], text=True).splitlines()
        prefixes = tuple(r[0] + "_fmi3" for r in recipes)
        self.assertTrue(all(line.split()[-1].startswith(prefixes) for line in exports))
        combined_api = C.CDLL(str(combined))
        for name, *_ in recipes:
            version = getattr(combined_api, name + "_fmi3GetVersion")
            version.argtypes, version.restype = [], C.c_char_p
            self.assertEqual(version(), b"3.0")


if __name__ == "__main__":
    unittest.main(verbosity=2)
