# ohua-standalone

## Installing

Required tools:

- `stack` https://haskellstack.org

### Instructions

1. Clone the repository

    `git clone https://github.com/ohua-dev/ohuac`

2. Build the program

   `stack install`

   This downloads and builds all dependencies, as well as the Haskell compiler
   `ghc`, should it not be present already. It should not interfere with any
   system-level libraries, Haskell ecosystems etc.

   It builds the executable `ohuac` and copies it to `~/.local/bin`. If you do
   not wish this use `stack build` instead and find the path of the binary using
   `stack exec -- which ohuac` afterwards

3. Explore the options for the compiler using `ohuac --help`


## Examples

The [test-resources](test-resources) directory contains examples namespaces
using both the ohua S-Expression syntax (ohuas) and C/Rust-like syntax (ohuac).
