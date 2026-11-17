# Formal verification

Mutation checks measure whether a model's existing properties detect a planted change.

## Language

**Matrix execution plan**

The ordered TLC runs for a matrix, with the checks in effect at each run. Each reach check belongs to the first matching run in its own spec section, even when another section names the same spec.

**Original check**

A theorem, example or guard in the unmutated Lean model. A mutation failure can be attributed to it when the same check has the same elaborated statement in the mutant. For an example or guard, that identity includes the particular occurrence in the source.
