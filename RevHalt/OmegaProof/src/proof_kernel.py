"""
Ω_proof Kernel — Strict Finite-Domain T1 Kernel

This module implements a rigorous, finite-domain "executable theory" of RevHalt.
It adheres to the 10-point Strict Specification provided by the user.

1. SCOPE: Finite Traces {0..bound-1} -> Bool.
2. DEFINITIONS: Strict analogs of Lean definitions.
3. UNIVERSAL VERIFICATION: (See test_strict_t1.py)
4. EXOTIC KIT: Demonstrably non-standard on non-monotone traces.
5. API: Rev0_K is the sole public entry point for decisions.

"""

from dataclasses import dataclass
from typing import Callable, Set
from abc import ABC, abstractmethod
from enum import Enum
import random

# ============================================================================
# 1. LOGICAL PRIMITIVES (Finite Domain)
# ============================================================================

# TraceFn represents a predicate on ℕ.
TraceFn = Callable[[int], bool]

@dataclass
class FiniteTrace:
    fn: TraceFn
    bound: int
    
    def check(self, n: int) -> bool:
        """
        Evaluate T(n). Enforces False for out-of-bounds.
        Strictly total: handles negative indices by returning False.
        """
        if n < 0: return False
        if n >= self.bound: return False
        return self.fn(n)

# Alias for compatibility
Trace = FiniteTrace

def Halts(T: FiniteTrace) -> bool:
    """
    Standard Halting: ∃ n, T n.
    Interpreted as ∃ n < bound, T n (since T n is False thereafter).
    """
    return any(T.check(n) for n in range(T.bound))

def Monotone(T: FiniteTrace) -> bool:
    """Finite-domain Monotone: ∀ n,m < bound, n ≤ m → (T(n) → T(m))."""
    active = False
    for n in range(T.bound):
        val = T.check(n)
        if active and not val:
            return False
        if val:
            active = True
    return True

def up(T: FiniteTrace) -> FiniteTrace:
    """
    Cumulative operator: up(T)(n) := ∃ k ≤ n, T k.
    Restricted strictly to the finite scope.
    """
    def up_fn(n: int) -> bool:
        # Strict bounds check matching FiniteTrace contract
        if n < 0 or n >= T.bound:
            return False
        # Search range matching definition ∃ k ≤ n
        for k in range(0, n + 1):
            if T.check(k):
                return True
        return False
        
    return FiniteTrace(up_fn, T.bound)


# ============================================================================
# 2. KIT DEFINITION (Kit.lean)
# ============================================================================

@dataclass
class RHKit:
    Proj: Callable[[FiniteTrace], bool]

def Rev0_K(K: RHKit, T: FiniteTrace) -> bool:
    """Rev0_K K T := K.Proj (up T)"""
    return K.Proj(up(T))


# ============================================================================
# 3. EXOTIC KIT (Point 7)
# ============================================================================

def _exotic_proj(T: FiniteTrace) -> bool:
    """
    A non-standard observer for demonstration.
    - On Monotone traces: MUST behave like Halts(T).
    - On specific non-monotone traces (e.g. 0->1->0): returns False.
    """
    # Check for specific non-monotone pattern 0, 1, 0...
    if T.bound >= 3:
        if not T.check(0) and T.check(1) and not T.check(2):
            return False # "Glitched sensor"
            
    return Halts(T)

ExoticKit = RHKit(Proj=_exotic_proj)

def exotic_witness(bound: int) -> FiniteTrace:
    """Construct explicit witness for Point 7."""
    if bound < 3:
        raise ValueError("bound must be >= 3")
    bits = [False] * bound
    bits[1] = True  # 0,1,0,...
    bt = tuple(bits)
    return FiniteTrace(lambda n, bt=bt: bt[n], bound)


# ============================================================================
# 4. FORMULA LOGIC
# ============================================================================

class Formula(ABC):
    @abstractmethod
    def atoms(self) -> Set[str]: pass
    @abstractmethod
    def eval(self, assignment: dict) -> bool: pass
    @abstractmethod
    def depth(self) -> int: pass

@dataclass(frozen=True)
class Atom(Formula):
    name: str
    def atoms(self): return {self.name}
    def eval(self, a): 
        if self.name not in a: raise ValueError(f"Atom {self.name} not in assignment")
        return a[self.name]
    def depth(self): return 0
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Not(Formula):
    f: Formula
    def atoms(self): return self.f.atoms()
    def eval(self, a): return not self.f.eval(a)
    def depth(self): return 1 + self.f.depth()
    def __repr__(self): return f"¬{self.f}"

@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    def atoms(self): return self.left.atoms() | self.right.atoms()
    def eval(self, a): return self.left.eval(a) and self.right.eval(a)
    def depth(self): return 1 + max(self.left.depth(), self.right.depth())
    def __repr__(self): return f"({self.left} ∧ {self.right})"

@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    def atoms(self): return self.left.atoms() | self.right.atoms()
    def eval(self, a): return self.left.eval(a) or self.right.eval(a)
    def depth(self): return 1 + max(self.left.depth(), self.right.depth())
    def __repr__(self): return f"({self.left} ∨ {self.right})"

@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula
    def atoms(self): return self.left.atoms() | self.right.atoms()
    def eval(self, a): return (not self.left.eval(a)) or self.right.eval(a)
    def depth(self): return 1 + max(self.left.depth(), self.right.depth())
    def __repr__(self): return f"({self.left} → {self.right})"

class QuestionType(Enum):
    TAUT = 0
    SAT = 1

def formula_to_trace(formula: Formula, q_type: QuestionType) -> FiniteTrace:
    atom_list = sorted(formula.atoms())
    n_atoms = len(atom_list)
    bound = 2 ** n_atoms if n_atoms > 0 else 1
    
    if n_atoms == 0:
        val = formula.eval({})
        target = (not val) if q_type == QuestionType.TAUT else val
        return FiniteTrace(lambda n: target if n == 0 else False, 1)

    def check(n: int) -> bool:
        if n < 0 or n >= bound: return False
        bits = [(n >> i) & 1 for i in range(n_atoms)]
        assignment = {atom_list[i]: bool(bits[i]) for i in range(n_atoms)}
        result = formula.eval(assignment)
        if q_type == QuestionType.TAUT:
            return not result
        else:
            return result
            
    return FiniteTrace(check, bound)

def random_formula(n_atoms: int, max_depth: int, seed: int = None) -> Formula:
    if seed is not None: random.seed(seed)
    atoms = [Atom(f"p{i}") for i in range(n_atoms)]
    def gen(d):
        if d >= max_depth or (d > 0 and random.random() < 0.3): return random.choice(atoms)
        op = random.choice([Not, And, Or, Implies])
        if op == Not: return Not(gen(d+1))
        return op(gen(d+1), gen(d+1))
    return gen(0)


# ============================================================================
# 5. API PUBLIC (Point 6)
# ============================================================================

def verdict(formula: Formula, q_type: QuestionType) -> bool:
    """Core decision procedure via Rev0_K."""
    T = formula_to_trace(formula, q_type)
    return Rev0_K(ExoticKit, T)

def is_tautology(formula: Formula) -> bool:
    """T1: Tautology iff ¬Rev0_K(CounterExample)"""
    return not verdict(formula, QuestionType.TAUT)

def is_satisfiable(formula: Formula) -> bool:
    """T1: Satisfiable iff Rev0_K(Witness)"""
    return verdict(formula, QuestionType.SAT)

__all__ = [
    # Core trace layer
    "FiniteTrace",
    "Trace",
    "Halts",
    "Monotone",
    "up",

    # Kit layer
    "RHKit",
    "Rev0_K",
    "ExoticKit",
    "exotic_witness",

    # Formula layer
    "Formula",
    "Atom",
    "Not",
    "And",
    "Or",
    "Implies",
    "QuestionType",
    "formula_to_trace",

    # Public decision API
    "verdict",
    "is_tautology",
    "is_satisfiable",
]
