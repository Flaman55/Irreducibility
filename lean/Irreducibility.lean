module

public import Irreducibility.Defs
public import Irreducibility.Ticking
public import Irreducibility.Euclid
public import Irreducibility.Drum
public import Irreducibility.Bridge
public import Irreducibility.Compare

/-!
# Irreducibility -- Lean 4 formalization

Rings of arbitrary periods, composite periods included, are combined into a drum level by
level; relations between rings are read by ticking and common parts by Euclid's procedure
on relations. The development shows which rings contribute their whole period and how the
level sizes of the consecutive rings `2, 3, ..., n` are determined.
-/
