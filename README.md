# ompdart_extension
extension of https://github.com/lmarzen/ompdart to detect data race

# switch to branch 'extension'

# Data race detection support
Currently, DRS only supports data race detection on one target loop.
Users can specify the target parallel loop by placing '#pragma drd' right on top of the loop 
(DRS does not work if there is an empty line or another pragma between '#pragma drd' and the target for-loop.)
Current implementation does not care about OpenMP constructs, rather DRS currently serves as a tool to see if
there can be a data race if the user wants to parallelize a target loop (essentially the same as detecting data race in #pragma omp parallel for).
Future work will remove '#pragma drd' and do the analysis based on the OpenMP constructs.



# Requirements
1. OMPDart requirements
2. Python 3.8.10 (tested)
3. Z3 Python (4.13.2, but may work with other versions)


 
