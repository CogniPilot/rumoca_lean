"""Independent archive, schema, importer and raw FMI ABI regression checks.

This is test infrastructure, not compiler implementation or a formal certificate.
Run inside the Nix shell: python3 tests/fmi3.py MODEL.fmu SECOND_MODEL.fmu
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


FMU = Path(sys.argv.pop(1)).resolve()
PEER_FMU = Path(sys.argv.pop(1)).resolve()
VENDOR = Path(__file__).resolve().parents[1] / "packages/backend-fmi3/vendor/fmi3"
D, B, N, VR, P = C.c_double, C.c_bool, C.c_size_t, C.c_uint32, C.c_void_p
OK, DISCARD, ERROR = 0, 2, 3
LOG = C.CFUNCTYPE(None, P, C.c_int, C.c_char_p, C.c_char_p)


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
        h = self.create("me")
        self.assertEqual(self.EnterInitializationMode(h, False, 0, 0, False, 0), OK)
        out = (D * 1)()
        for method in [self.GetContinuousStates, self.GetContinuousStateDerivatives,
                       self.GetNominalsOfContinuousStates]:
            self.assertEqual(method(h, out, 1), OK)
        self.assertEqual(self.GetEventIndicators(h, None, 0), OK)
        self.assertEqual(self.ExitInitializationMode(h), OK)
        self.assertEqual(self.GetContinuousStateDerivatives(h, out, 1), OK)
        self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, (D * 1)(2), 1), OK)
        flags, next_time = [B() for _ in range(5)], D()
        self.assertEqual(self.UpdateDiscreteStates(h, *map(C.byref, flags), C.byref(next_time)), OK)
        self.assertEqual(self.EnterContinuousTimeMode(h), OK)
        self.assertEqual(self.SetFloat64(h, (VR * 1)(1), 1, (D * 1)(4), 1), OK)
        self.assertEqual(self.SetContinuousStates(h, (D * 1)(7), 1), OK)
        self.assertEqual(self.values(h), (0, 7, 1))
        count = N(99)
        self.assertEqual(self.GetNumberOfContinuousStates(h, C.byref(count)), OK)
        self.assertEqual(count.value, 1)
        self.assertEqual(self.GetNumberOfEventIndicators(h, C.byref(count)), OK)
        self.assertEqual(count.value, 0)
        self.assertEqual(self.Terminate(h), OK)
        final = (D * 1)()
        for getter, expected in [(self.GetContinuousStates, 7),
                                 (self.GetContinuousStateDerivatives, 1),
                                 (self.GetNominalsOfContinuousStates, 1)]:
            self.assertEqual(getter(h, final, 1), OK)
            self.assertEqual(final[0], expected)
        self.assertEqual(self.GetEventIndicators(h, None, 0), OK)
        self.assertEqual(self.GetNumberOfContinuousStates(h, C.byref(count)), OK)
        self.assertEqual(count.value, 1)
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

    def test_invalid_arguments_and_output_atomicity(self):
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
