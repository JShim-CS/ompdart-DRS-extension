# Data race detection support
Currently, DRS only supports data race detection on one target loop. Users can specify the target parallel loop by placing '#pragma drs' right on top of the loop (DRS does not work if there is an empty line or another pragma between '#pragma drs' and the target for-loop.) Current implementation does not care about OpenMP constructs, rather DRS currently serves as a tool to see if there can be a data race if the user wants to parallelize a target loop (essentially the same as detecting data race in #pragma omp parallel for). Future work will remove '#pragma drs' and do the analysis based on the OpenMP constructs.

# Dependencies

- [OMPDart](https://github.com/lmarzen/ompdart) (included)
- Python 3.8.10 (tested)
- Z3 Python (4.13.2, but may work with other versions)
- Clang 16+ 
- Boost C++ Libraries

# drsolver.py
For correct detection results, always delete drsolver.py before running the analysis.
Uncommmenting line 52 of "run.sh" will automatically delete drsolver.py after the analysis.

Below are ReadMe from OMPDART

# OMPDart
OMPDart - OpenMP Data Reduction Tool
OMPDart is a C/C++ static source code transformation tool for automatically generating efficient OpenMP GPU data mapping.

### Usage
To build OMPDart run the following script.
```bash
bash build.sh
```

Run OMPDart on a C/C++ source code file with OpenMP offload directives (but without target data mapping constructs). The transformed code with data mappings will be output into `<output_file>`.
```bash
bash run.sh -i <input_file> -o <output_file>
```
The DRS extension will additionally detect the presence of a data race for do-all parallel or simd loop




