# ROOPLInt

*ROOPLInt* is an interpreter for running source code written in **Reversible Object Oriented Programming Language++** (ROOPL++).

The backbone, everything from parsing to type checking, is forked from Martin Cservenka's [ROOPLPPC repository](https://github.com/cservenka/ROOPLPPC), as the scope of this project is to be able to run ROOPL(++) code without compiling to PISA.

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
