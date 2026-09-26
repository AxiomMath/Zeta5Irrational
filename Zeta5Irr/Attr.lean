module

public meta import Lean

/-!
# The `zeta5irr` tag attribute

Marks a declaration as formalizing a blueprint entity. The dashboard's source
walker reads it, writes `lean_decl` / `lean_loc` back into the audit row, and the
entity stops rendering grey.

Place it by the covering-set rule: on the declarations whose union states the
entity's content, never on scaffolding.

Write it as the attribute name, then the blueprint tag in quotes, on the line
above the declaration it covers.

This paragraph deliberately does not show the syntax literally. A scanner that
does not strip comments reads an example as a real tag: the dashboard's source
walker did, and reported every freshly scaffolded project as having one tagged
Lean entity referencing a tag that is in no blueprint. Show the shape in prose,
or in a file the walker does not read.
-/

public meta section

open Lean

/-- Links a Lean declaration to a blueprint tag: the attribute name, then the
tag in quotes. Not written literally here — see the module docstring. -/
syntax (name := zeta5irr) "zeta5irr " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `zeta5irr
  descr := "marks a declaration as formalizing a blueprint entity"
  add   := fun _ _ _ => pure ()
}

end
