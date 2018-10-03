# The standalone Ohua compiler: `ohuac`

[![Build Status](https://travis-ci.org/ohua-dev/ohuac.svg?branch=master)](https://travis-ci.org/ohua-dev/ohuac)
[![Latest Release](https://img.shields.io/github/release/ohua-dev/ohuac.svg)](https://github.com/ohua-dev/ohuac/releases/latest)

For the complete documentation of the `ohuac` compiler see the [standalone
compiler section of the ohua
documentation](https://ohua.readthedocs.org/en/latest/ohuac.html)

## Usage

For a complete list of the options available use the `--help` flag.

## Installing

Prebuilt binaries are available for 64bit Linux and OSX. Provided for each
release by [Travis CI](https://travis-ci.org/ohua-dev/ohuac).

Simply download the appropriate executable for you platform (`ohuac-linux` or
`ohuac-osx`) from the [releases page](https://github.com/ohua-dev/ohuac/releases/latest).

## Building from source

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


## Examples

The [test-resources](test-resources) directory contains example namespaces
using both the ohua S-Expression syntax (`ohuas`) and C/Rust-like syntax (`ohuac`).
