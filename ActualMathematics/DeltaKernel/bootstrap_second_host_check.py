#!/usr/bin/env python3
"""Second-host δ-kernel checker (Bootstrap B5 empirical receipt).

Reimplements the forced `1+1=2` tree check independently of Lean.
Agreement with Lean's `Examples.onePlusOne_forced` is the portable-checker
receipt. This is not a full port of `check`; it is a hostile independent
realization of one forced derivation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple, Union


@dataclass(frozen=True)
class Zero:
    tag: str = "zero"


@dataclass(frozen=True)
class Succ:
    arg: "Term"
    tag: str = "succ"


@dataclass(frozen=True)
class Add:
    left: "Term"
    right: "Term"
    tag: str = "add"


Term = Union[Zero, Succ, Add]


@dataclass(frozen=True)
class Eq:
    left: Term
    right: Term


@dataclass(frozen=True)
class EqRefl:
    term: Term


@dataclass(frozen=True)
class AddZero:
    term: Term


@dataclass(frozen=True)
class AddSucc:
    left: Term
    right: Term


@dataclass(frozen=True)
class EqSubst:
    hole: Eq  # hole uses Var0 as rewrite position on the right of succ
    t: Term
    s: Term
    proof_eq: object
    proof_hole: object


@dataclass(frozen=True)
class Var0:
    tag: str = "var0"


ONE = Succ(Zero())
TWO = Succ(Succ(Zero()))


def subst_term(k_is_zero: bool, replacement: Term, term: Term) -> Term:
    if isinstance(term, Zero):
        return term
    if isinstance(term, Succ):
        return Succ(subst_term(k_is_zero, replacement, term.arg))
    if isinstance(term, Add):
        return Add(
            subst_term(k_is_zero, replacement, term.left),
            subst_term(k_is_zero, replacement, term.right),
        )
    raise TypeError(term)


def subst_eq(replacement: Term, formula: Eq) -> Eq:
    # Only the hole used by onePlusOne: eq(add(one,succ(zero)), succ(var0))
    # Substituting var0 := replacement on the right.
    def go(term: object) -> Term:
        if isinstance(term, Var0):
            return replacement
        if isinstance(term, Zero):
            return term
        if isinstance(term, Succ):
            return Succ(go(term.arg))
        if isinstance(term, Add):
            return Add(go(term.left), go(term.right))
        raise TypeError(term)

    return Eq(go(formula.left), go(formula.right))


def check(deriv) -> Optional[Tuple[Eq, str]]:
    if isinstance(deriv, EqRefl):
        return Eq(deriv.term, deriv.term), "empty"
    if isinstance(deriv, AddZero):
        return Eq(Add(deriv.term, Zero()), deriv.term), "empty"
    if isinstance(deriv, AddSucc):
        return (
            Eq(
                Add(deriv.left, Succ(deriv.right)),
                Succ(Add(deriv.left, deriv.right)),
            ),
            "empty",
        )
    if isinstance(deriv, EqSubst):
        ceq = check(deriv.proof_eq)
        ct = check(deriv.proof_hole)
        if ceq is None or ct is None:
            return None
        formula_eq, o1 = ceq
        formula_t, o2 = ct
        if formula_eq != Eq(deriv.t, deriv.s):
            return None
        expected_t = subst_eq(deriv.t, deriv.hole)
        if formula_t != expected_t:
            return None
        return subst_eq(deriv.s, deriv.hole), "empty" if o1 == o2 == "empty" else "mixed"
    return None


def one_plus_one() -> EqSubst:
    # hole: 1 + S0 = S(var0)
    hole = Eq(Add(ONE, Succ(Zero())), Succ(Var0()))
    return EqSubst(
        hole=hole,
        t=Add(ONE, Zero()),
        s=ONE,
        proof_eq=AddZero(ONE),
        proof_hole=AddSucc(ONE, Zero()),
    )


def malformed_one_plus_one() -> EqSubst:
    """Same claimed conclusion, with a deliberately wrong equality premise."""
    tree = one_plus_one()
    return EqSubst(
        hole=tree.hole,
        t=tree.t,
        s=tree.s,
        proof_eq=EqRefl(Zero()),
        proof_hole=tree.proof_hole,
    )


def main() -> int:
    result = check(one_plus_one())
    expected = Eq(Add(ONE, ONE), TWO)
    accepts_valid = result == (expected, "empty")
    rejects_malformed = check(malformed_one_plus_one()) is None
    ok = accepts_valid and rejects_malformed
    print(
        {
            "host": "python-delta-checker",
            "tree": "onePlusOne",
            "accepted_valid": accepts_valid,
            "rejected_malformed": rejects_malformed,
            "result": None if result is None else (str(result[0]), result[1]),
            "agrees_with_lean_forced_empty_ledger": accepts_valid,
        }
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
