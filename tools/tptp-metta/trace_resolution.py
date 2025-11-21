#!/usr/bin/env python3
"""
Trace pyprover resolution on a simple problem to understand the algorithm
"""

from pyprover import *

# Simple problem: (p | q), (~p | r) |- (q | r)
# In pyprover syntax:
p = Atom('p')
q = Atom('q')
r = Atom('r')

# Clause 1: p | q
clause1 = p | q

# Clause 2: ~p | r
clause2 = ~p | r

print("=" * 60)
print("SIMPLE RESOLUTION EXAMPLE")
print("=" * 60)
print(f"Clause 1: {clause1}")
print(f"Clause 2: {clause2}")
print()

# Resolve them
print("Calling: clause1.resolve_against(clause2)")
print()

# This should give us: q | r
resolvents = clause1.resolve_against(clause2)

print(f"Result type: {type(resolvents)}")
print(f"Result: {resolvents}")
print()

if isinstance(resolvents, list):
    for i, resolvent in enumerate(resolvents):
        print(f"Resolvent {i+1}: {resolvent}")
        print(f"  Type: {type(resolvent)}")
        if hasattr(resolvent, 'args'):
            print(f"  Args: {resolvent.args}")
print()

# Let's trace a knights and knaves style problem
print("=" * 60)
print("KNIGHTS AND KNAVES STYLE PROBLEM")
print("=" * 60)

knight_a = Atom('knight_a')
knave_a = Atom('knave_a')
knight_b = Atom('knight_b')
knave_b = Atom('knave_b')

# Axioms (simplified)
axiom1 = knight_a | knave_a         # A is knight or knave
axiom2 = ~knight_a | ~knave_a       # A is not both
axiom3 = knight_b | knave_b         # B is knight or knave
axiom4 = ~knight_b | ~knave_b       # B is not both

clauses = [axiom1, axiom2, axiom3, axiom4]

print("Axioms:")
for i, clause in enumerate(clauses, 1):
    print(f"  {i}. {clause}")
print()

# Try resolving axiom1 and axiom2
print(f"Resolving: {axiom1} with {axiom2}")
result = axiom1.resolve_against(axiom2)
print(f"Result: {result}")
print()

# Show internal structure
print("=" * 60)
print("INTERNAL STRUCTURE")
print("=" * 60)
print(f"clause1 type: {type(clause1)}")
print(f"clause1.__class__.__name__: {clause1.__class__.__name__}")

if hasattr(clause1, '__dict__'):
    print(f"clause1 attributes: {clause1.__dict__}")

# Check the Or class methods
from pyprover.logic import Or
print(f"\nOr class methods: {[m for m in dir(Or) if not m.startswith('_')]}")
