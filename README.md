# ROOPLInt

*ROOPLInt* is an interpreter for running source code written in **Reversible Object Oriented Programming Language++** (ROOPL++).

The backbone, everything from parsing to type checking, is forked from Martin Cservenka's [ROOPLPPC repository](https://github.com/cservenka/ROOPLPPC), as the scope of this project is to be able to run ROOPL(++) code without compiling to PISA.

For ease of use when building/testing, see the `Makefile`.

## Requirements

ROOPLInt uses [Stack](https://docs.haskellstack.org/en/stable/README/) to manage all dependencies and requirements.

## Building

Simply invoke
```
stack build
```
which compiles an executable into the `.stack-work` folder

## Usage

**TODO**
To run the ROOPL interpreter, do the following
```
stack exec ROOPLInt input.rplpp
```
which interprets the input program and execute it directly.

## Examples

To see usage examples, please refer to `test/` for example programs. 

## Web Interface

The solution contains a web service for running the interpreter, inverter and for compiling without the need of having to build and install the dependencies.

The web interface, in `web/`, is based on the web interface for the Janus interpreter from the project [jana](https://github.com/mbudde/jana).
The web interface contains a different license, which can be found in the `web/` folder.

To ease of setting up and ensuring reproducability of the web service, this solution contains a `Dockerfile`.
The `Dockerfile` builds the `ROOPLInt` project and then copies the executable to the web interface, along with the test examples.
