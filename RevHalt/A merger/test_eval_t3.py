"""
test_eval_t3.py — Smoke test for exact policy metrics.

Uses StubS1 from test_t3_policy.py.
"""

from test_t3_policy import StubS1, mk_trace
from t3_policy import T3HaltingPolicy
from eval_t3 import exact_metrics_policy, monotone_failure_cases


def test_exact_metrics(bound: int = 10):
    policy = T3HaltingPolicy(s1=StubS1(bound), eps=0.10)
    m = exact_metrics_policy(policy, bound)
    assert m.total == 2 ** bound
    # S2 should cover all monotone traces (bound+1). S1 covers the rest.
    assert m.source_counts.get("S2", 0) == (bound + 1)
    assert len(monotone_failure_cases(policy, bound)) == 0


if __name__ == "__main__":
    test_exact_metrics(10)
    print("PASS")
