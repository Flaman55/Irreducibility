module

public import Irreducibility.Defs
public import Irreducibility.Residues
public import Irreducibility.SechComb
public import Irreducibility.Euclid
public import Irreducibility.Radices
public import Irreducibility.InitialModuli
public import Irreducibility.Compare
public import Irreducibility.Blocks
public import Irreducibility.Primality
public import Irreducibility.Atoms
public import Irreducibility.Arithmetic

/-!
# Irreducibility -- Lean 4 formalization

A residue number system over arbitrary moduli, composite and not pairwise coprime moduli
included: residues are computed by counting, gcds by Euclid's algorithm on residues, and the
moduli are combined into a mixed-radix system. The development shows which moduli receive
their whole value as radix, how the radices of the consecutive moduli `2, 3, ..., n` are
determined, and how comparison, overflow detection, exact division, base extension and
primality testing are computed on residues without assembling the number.
-/
