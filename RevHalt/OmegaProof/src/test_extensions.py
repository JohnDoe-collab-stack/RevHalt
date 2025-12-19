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
    # Skip if torch not installed
    try:
        import torch
    except Exception:
        return

    from ml_bridge import trace_from_model
    from proof_kernel import Atom, Or, Not, QuestionType

    # Dummy model: returns 1.0 only for n==0
    class DummyIndexModel:
        def __call__(self, x):
            n = int(x.reshape(-1)[0].item())
            return 1.0 if n == 0 else 0.0

    p = Atom("p")
    f = Or(p, Not(p))  # just to get a bound=2

    T = trace_from_model(DummyIndexModel(), f, QuestionType.SAT, threshold=0.5)
    assert T.bound == 2
    assert T.check(-1) is False
    assert T.check(0) is True
    assert T.check(1) is False
    assert T.check(2) is False


def test_kit_from_model_basic():
    try:
        import torch
    except Exception:
        return

    from ml_bridge import kit_from_model
    from proof_kernel import FiniteTrace

    # Dummy model: predicts halts iff any bit is 1
    class DummyBitsModel:
        def __call__(self, x):
            # x shape [1,bound]
            return float(x.sum().item() > 0.0)

    K = kit_from_model(DummyBitsModel(), threshold=0.5)
    T0 = FiniteTrace(lambda n: False, 5)
    T1 = FiniteTrace(lambda n: (n == 3), 5)

    assert K.Proj(T0) is False
    assert K.Proj(T1) is True


def test_regression_strict_suite_importable():
    # Ensures the strict suite still imports cleanly after adding __all__
    import test_strict_t1  # noqa: F401


if __name__ == "__main__":
    test_kernel_exports()
    test_trace_from_model_totality()
    test_kit_from_model_basic()
    test_regression_strict_suite_importable()
    print("PASS")
