# Prerequests

* Compiler: Clang 17+ / MSVC 14.34+
* Cmake: 3.28+
* Generator: Ninja 1.11+ / VS 2022+
* Python: 3.6+
* Boost: 1.40+

# Build project
## Unix
* Ether set env variables **CMAKE** and **NINJA** with /full/path to binaries or add directory to **PATH** 
* Also you can set **BUILD** env variable to specify path for binaries (default is *build*)
* Run **make**
* Test binary in *BUILD* folder.

Example:
```bash
CMAKE=/full/path/to/cmake NINJA=/full/path/to/ninja make
./install/test
./install/testCompile
```

## Windows
Example:
```bash
/full/path/to/cmake -G "Visual Studio 17 2022"
/full/path/to/cmake --build /path/to/build
```

# Usage examples
## Prepairing
Before running the benchmarks be sure that the project is successfully built.  
To run tests:
```bash
build/test
```
To run bench:
```bash
build/bench -h
```
You'll need to download third-party benchmarks input files meet the [CNF Format](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/satformat.ps).  
For example from [here](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).

## Running the benchmarks and plotting graphs
This example will store all results of running every algorithm on every file from `/PATH/TO/uf20_91/` in `uf20_91.txt` and then build plots based on it.
```bash
python3 benchmark.py -dir /PATH/TO/uf20_91 -o uf20_91.txt
```

You can also specify multiple input directories and output files. The results of each new directory will be saved in a new output file. If the number of specified output files is less than the number of input directories, additional results will be printed in `stdout`.
```bash
python3 benchmark.py -dir /PATH/TO/uf50_218 /PATH/TO/uf75_325 -o uf50_218.txt uf75_325.txt
```
## Just plotting graphs
This example will read results from `uf20_91.txt` and then build plots based on it.
```bash
python3 benchmark.py -o uf20_91.txt
```