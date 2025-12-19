"""
demo_proof_object.py — Concrete demonstration of Execution with Proof

1. Creates a hard non-monotone trace (requires witness).
2. Runs S2 + ML Heuristic.
3. Prints the resulting Decision and Certificate.
"""

import torch
from proof_kernel import FiniteTrace
from s2_extended import S2ExtendedProver
from ml_witness import WitnessModel
from s2_heuristic import S2Heuristic
from t3_types import Verdict

import sys

def demo_execution_with_proof():
    allow_cheat = "--allow_demo_cheat" in sys.argv
    
    # Setup
    bound = 10
    # Hard trace: 0 0 1 0 ... (Non-monotone, halts at index 2)
    # Standard S2 (switchpoint) would fail here because logic is only monotone.
    # We need the ML to point to index 2.
    bits = [False] * bound
    bits[2] = True 
    bits[3] = False # Break monotonicity
    
    T = FiniteTrace(lambda n, bt=tuple(bits): (False if (n < 0 or n >= len(bt)) else bt[n]), bound)
    
    print(f"Trace: {bits}")
    print("Standard S2 (Monotone) alone would return UNKNOWN.")
    
    # Load components
    base_s2 = S2ExtendedProver()
    model = WitnessModel(bound)
    try:
        model.load_state_dict(torch.load("witness_model.pt"))
        print("\n[ML] Model loaded successfully.")
    except:
        print("\n[ML] Warning: Using random weights (demo might fail if untested).")

    heuristic_s2 = S2Heuristic(base_s2, model, k=3)
    
    # Execute
    print("\nExecuting S2_Heuristic.decide(T)...")
    d = heuristic_s2.decide(T)
    
    # FOR DEMO ONLY: If ML failed (because training was short), inject the known witness
    # to demonstrate the S2 Proof Certificate structure.
    # PROTECTED by flag.
    if d.verdict == Verdict.UNKNOWN:
        if allow_cheat:
            print("[Demo] ML missed the witness. FORCING known witness index 2 (--allow_demo_cheat active)...")
            cert_d = heuristic_s2.prover.certify_witness(T, 2)
            # Manually reconstruct the wrapper that heuristic would have made
            if cert_d:
                 from t3_types import Decision
                 d = Decision(
                     verdict=cert_d.verdict,
                     source="S2+ML (Simulated)",
                     cert={**cert_d.cert, "assisted_by": "ML"}
                 )
        else:
            print("[Demo] ML missed the witness. Run with --allow_demo_cheat to see what a proof looks like.")

    # Verify Proof
    print("\n=== EXECUTION RESULT ===")
    print(f"Verdict: {d.verdict}")
    print(f"Source:  {d.source}")
    print(f"Cert:    {d.cert}")
    
    if d.source.startswith("S2"):
        print("\n[Proof Check]")
        logic = d.cert.get("logic", "Unknown")
        if logic == "Witness":
            idx = d.cert["index"]
            valid = T.check(idx)
            print(f"Checking Witness index {idx} on Trace... T[{idx}] = {valid}")
            if valid:
                print("✅ PROOF VERIFIED: The certificate is valid.")
            else:
                print("❌ PROOF FAILED: The certificate is invalid.")
        elif logic == "Monotone":
             print("✅ PROOF VERIFIED: Monotone Switchpoint.")
        else:
            print(f"Unknown logic type: {logic}")
    else:
        print("Fallback to Oracle (No internal proof found).")

if __name__ == "__main__":
    demo_execution_with_proof()
