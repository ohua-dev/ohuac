# Release 0.3.0

## Features

### Stateful functions

This release features the first version of the explicit state proposal
(ohua-dev/ohua-core#22). With the following changes

- Rust, ML and S-Expression frontend support of the `function with state` syntax
  which associates `function` with the state formed by the expression `state`.
  Functions bound thus are stateful functions and are treated differently.
  Functions not bound to a state are stateless functions.
- The JSON representation has changed to also include state arcs.

For the time being state is restricted to environment values or values bound in
the top level scope (i.e. not in an `if`, `smap` etc context).

### Rust Syntax

- Functions with no return expression (i.e. last expression is terminated with
  `;`) are now supported and implicitly return `()`
  (ohua-dev/alang-clike-parser#4)
- Syntax for lambdas has been tweaked to more closely resemble actual rust
  syntax with the form `| arg1, ... args | expr` or `| arg1, ... args | { stmts
  }` (ohua-dev/alang-clike-parser#10)
- Import syntax now also supports actual rust style with the forms
  `name::space::import_item` or `name::space::{import_item, ...items}`
  (ohua-dev/alang-clike-parser#6)
- Variable names beginning with `_` are no longer rejected by the parser. This
  also enables the use of `_` as an identifier for ignored values
  (ohua-dev/alang-clike-parser#5)
- Literals
  - `()` (empty parentheses) is accepted as a literal for the unit value
  - Numeric literals are supported i.e. `1`, `2`, `-100`
- Introduced the `with` keyword (operator) that binds a state to a function.

### ML Syntax

- Literals
  - `()` (empty parentheses) is accepted as a literal for the unit value
  - Numeric literals are supported i.e. `1`, `2`, `-100`
- Introduced the `with` keyword (operator) that binds a state to a function.

### S-Expression syntax

- Literals
  - `nil` is supported as a literal for the unit value
  - Numeric literals are supported i.e. `1`, `0`, `-1000` (due to the liberal
    rules for the names of clojure identifiers the `-` must not be followed by a
    space for it to be parsed as a literal)
- Imports now use `(require type [imports])` syntax where `type` is one of `sf` or `algo`
- Introduced the `with` special form that binds state to a function.

### Literals

ALang as well as the `.ohuaml`, `.ohuac` and `.ohuas` formats now support
numeric literals and a unit literal. (ohua-dev/ohua-core#23)

In general the literals for `()` are supported both as expressions as well as in
patterns. Integer literals are currently not supported in patterns.

**Caveat:** The backend implementation does not necessarily properly support
these literals. (Specifically the generated java code most likely breaks when
using literals.)

### New intermediate language

A new, rich frontend intermediate language has been introduced
(ohua-dev/ohua-core#23). This enabled the following features:

- Features of the individual parsers are now more similar, as they do not need
  to be desugared in the parser itself but are handled uniformly by the compiler.
- Destructuring/pattern matching is now a desugaring feature and supports
  arbitrarily nested patterns. (ohua-dev/ohua-core#17)

## Breaking changes

- The JSON representation changed to incorporate state arcs and compound arcs.
  As a result the `"arcs"` key in the JSON now contains an object with the keys
  `"direct"` for direct (or classic) arcs, `"compound"` for arcs where multiple,
  local sources are combined into a single argument and `"state"` which lists
  arcs to be set as the state of a function.
