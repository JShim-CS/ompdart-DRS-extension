# Data race detection support
Currently, DRS only supports data race detection on one target loop. Users can specify the target parallel loop by placing '#pragma drs' right on top of the loop (DRS does not work if there is an empty line or another pragma between '#pragma drs' and the target for-loop.) Current implementation does not care about OpenMP constructs, rather DRS currently serves as a tool to see if there can be a data race if the user wants to parallelize a target loop (essentially the same as detecting data race in #pragma omp parallel for). Future work will remove '#pragma drs' and do the analysis based on the OpenMP constructs.

# Requirements

OMPDart requirements

Python 3.8.10 (tested)

Z3 Python (4.13.2, but may work with other versions)

# drsolver.py
For correct detection results, always delete drsolver.py before running the analysis.
Uncommmenting line 52 of "run.sh" will automatically delete drsolver.py after the analysis.

Below are ReadMe from OMPDART

# OMPDart
OMPDart - OpenMP Data Reduction Tool

OMPDart is a C/C++ static analysis tool for automatically generating efficient OpenMP GPU data mapping.


### Usage

Dependencies:
- Clang 16+
- Boost C++ Libraries

To build OMPDart run the following script.
```bash
bash build.sh
```

Run OMPDart on a C/C++ source code file with OpenMP offload directives (but without target data mapping constructs). The transformed code with data mappings will be output into `<output_file>`.
```bash
bash run.sh -i <input_file> -o <output_file>
```


### Evaluation

```bash
cd evaluation
```

We provide the tool generated mappings in this repository, see source files with _ompdart in the file name. Tool-generated mappings can generated with `generate_ompdart_mappings.sh` which will run OMPDart on each benchmark and generate source code files with the .new extension.
```bash
bash generate_ompdart_mappings.sh
```

Benchmarks used for evaluation are in the sub directory `evaluation`. Some of these require data sets from the Rodinia suite.
Running the following command will automatically download and place the data sets in the correct path `evaluation/data`
```bash
bash download_dataset.sh
```

The `run_all.sh` script will build and run each version of each benchmark to gather execution time results.
```bash
bash run_all.sh
```

The `profile_all.sh` script will build and profile each version of each benchmark with NVIDIA Nsight Systems, used to results on data transfer time and CUDA memcpy calls.
```bash
bash profile_all.sh
```

