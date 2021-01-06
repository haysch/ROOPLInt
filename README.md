# ROOPLPP

*ROOPLPP* is an extension of the **Reversible Object Oriented Programming Language++** (ROOPL++) by Martin Cservenka's [ROOPLPPC repository](https://github.com/cservenka/ROOPLPPC).

*ROOPLPP* supports compilation, interpretation and program inversion of ROOPL++ source code.

The interpreter and program inverter is created as part of a university project.
The goal was to improve the usability of ROOPL.

For ease of use when building/testing, see the included `Makefile`.

## Requirements

ROOPLPP uses [Stack](https://docs.haskellstack.org/en/stable/README/) to manage all dependencies and requirements.

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
stack exec ROOPLPP input.rplpp
```
which interprets the input program and execute it directly.

## Examples

To see usage examples, please refer to `test/` for example programs. 

## Web Interface

The solution contains a web service for running the interpreter, inverter and for compiling without the need of having to build and install the dependencies.

The web interface, in `web/`, is based on the web interface for the Janus interpreter from the project [jana](https://github.com/mbudde/jana).
The web interface contains a different license, which can be found in the `web/` folder.

To ease of setting up and ensuring reproducability of the web service, this solution contains a `Dockerfile`.
The `Dockerfile` builds the `ROOPLPP` project and then copies the executable to the web interface, along with the test examples.
