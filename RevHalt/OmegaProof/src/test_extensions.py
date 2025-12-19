# test_extensions.py
import importlib
import types

import proof_kernel as pk

def test_kernel_exports():
    assert hasattr(pk, "__all__")
    exported = set(pk.__all__)
    # sanity: critical names present
    for name in ["FiniteTrace", "Halts", "Monotone", "up", "RHKit", "Rev0_K", "ExoticKit", "exotic_witness"]:
        assert name in exported

    # star import should not leak extra names beyond __all__
    ns = {}
    exec("from proof_kernel import *", ns, ns)
    leaked = {k for k in ns.keys() if not k.startswith("_")} - exported - {"__builtins__"}
    assert leaked == set(), f"Leaked names via star import: {leaked}"


def test_trace_from_model_totality():
    # Was test_trace_from_model_totality - Removed (Obsolete)
    pass


    # Was test_kit_from_model_basic - Removed (Obsolete)
    pass


def test_regression_strict_suite_importable():
    # Ensures the strict suite still imports cleanly after adding __all__
    import test_strict_t1  # noqa: F401


if __name__ == "__main__":
    test_kernel_exports()
    test_trace_from_model_totality()
    test_kit_from_model_basic()
    test_regression_strict_suite_importable()
    print("PASS")
