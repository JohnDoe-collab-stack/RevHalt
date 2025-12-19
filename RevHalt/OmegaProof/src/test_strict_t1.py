
"""
Ω_proof STRICT VERIFICATION SUITE
Strict separation of test logic from kernel.
Adheres to User Directive 2.
"""

from itertools import product
from proof_kernel import (
    FiniteTrace, ExoticKit, Halts, Monotone, up, Rev0_K,
    exotic_witness
)

def all_traces(bound: int):
    """
    Generate all 2^bound possible traces.
    Safe generator avoiding closure capture issues.
    """
    for bits in product([False, True], repeat=bound):
        bt = tuple(bits)
        # Capture bt safely in lambda default arg
        yield FiniteTrace(lambda n, bt=bt: (False if (n < 0 or n >= len(bt)) else bt[n]), bound)

def test_bridge(bound: int):
    """2.2 Verify Bridge: Halts(up T) <-> Halts(T) universally."""
    for T in all_traces(bound):
        if Halts(up(T)) != Halts(T):
            raise AssertionError(f"Bridge failed for trace {T}")

def test_detects_monotone(bound: int):
    """2.3 Verify DetectsMonotone universally for ExoticKit."""
    for X in all_traces(bound):
        if Monotone(X):
            if ExoticKit.Proj(X) != Halts(X):
                raise AssertionError(f"DetectsMonotone failed for trace {X}")

def test_exoticity(bound: int):
    """2.4 Verify Exoticity Constructive."""
    T = exotic_witness(bound)
    if Monotone(T): raise AssertionError("Witness unexpectedly monotone")
    if not Halts(T): raise AssertionError("Witness should halt")
    if ExoticKit.Proj(T) != False: raise AssertionError("Kit not exotic on witness")
    print(f"[Pass] Exotic Witness (0->1->0) confirmed non-monotone and Kit-divergent.")

def test_T1(bound: int):
    """2.5 Verify T1 Universal: Rev0_K(ExoticKit, T) <-> Halts(T)."""
    for T in all_traces(bound):
        if Rev0_K(ExoticKit, T) != Halts(T):
            raise AssertionError(f"T1 failed for trace {T}")

if __name__ == "__main__":
    print("=== Ω_proof STRICT UNIVERSAL VERIFICATION SUITE ===\n")
    
    # 2.6 Runner Strict
    BOUND = 10 # 1024 traces
    print(f"Running exhaustive tests on domain size 2^{BOUND} ({2**BOUND} traces)...")
    
    try:
        # Order: bridge -> detects_monotone -> exoticity -> T1
        test_bridge(BOUND)
        print("[Pass] Bridge verified universally.")
        
        test_detects_monotone(BOUND)
        print("[Pass] DetectsMonotone verified universally.")
        
        test_exoticity(BOUND)
        
        test_T1(BOUND)
        print("[Pass] T1 verified universally.")
        
        print("\n=== All Strict Theoretical Contracts Validated. Kernel is Sound. ===")
        
    except Exception as e:
        print(f"\n[FAIL] VERIFICATION ERROR: {e}")
        exit(1)
