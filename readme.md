# Smt2C
> Transforming SMT2 files into equivalent C tasks

Benchmarking of software verifiers is difficult.
Existing verification benchmarks are often too small to test every little detail of the verifier implementation and extended the benchmark often requires a significant manual effort.
With Smt2C, we introduce an easy way to generate a C benchmark from an SMT2 benchmark. 

Smt2C expects a SMT2 task and then creates a C task where an error location is reachable iff the SMT formula was satisfiable.
As a result, Smt2C can be used to create new benchmarks for C verifiers that test a larger variety of C features. 

## Installation
The package is tested under Python 3.10. It can be installed by cloning this repository and installing all requirements via:
```
pip install -r requirements.txt
```

## Quick start
Smt2C can transform one or ore files. To transform an existing benchmark (in the [SMT-COMP](https://github.com/SMT-LIB/benchmark-submission/blob/main/README.md) format), you can run the following script:
```bash
$ python run_transformations.py [input_files] -o [output_dir] [--parallel]
```
The script transforms the input files and writes the result in the output folder.
The input files may contain only .smt2 files.
If you transform multiple files, it can be beneficial to run the transformation in parallel (via the `--parallel` option).

The following scripts generated the examples.
They and their input files are a minimal example for how a benchmark might look like.
```bash
$ python src/run_transformations.py examples/test_sources/bvadd_char.smt2 examples/test_sources/bvadd_short.smt2 examples/test_sources/bvadd_int.smt2 examples/test_sources/bvadd_longlong.smt2 -o examples/bvadd_c
```
```bash
$ python src/run_transformations.py examples/test_sources/bvand_*.smt2 -o examples/bvand_c
```
```bash
$ python src/run_transformations.py examples/test_sources/*_short.smt2 -o examples/bvshort_c
```

## Project Info
Distributed under the MIT license. See ``license.txt`` for more information.