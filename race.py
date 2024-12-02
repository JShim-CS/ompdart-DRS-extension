# import os
# import re

# def replace_omp_pragmas(source_dir, dest_dir):
#     """
#     Replace `#pragma omp` directives (e.g., `#pragma omp parallel for private(...)`) with `#pragma drd` in `.c` and `.cpp` files.
#     Save the modified files in the specified destination directory.

#     Args:
#         source_dir (str): Path to the directory containing the source files.
#         dest_dir (str): Path to the directory to save the modified files.
#     """
#     # Ensure the destination directory exists
#     os.makedirs(dest_dir, exist_ok=True)

#     # Regular expression to match the entire OpenMP pragma line
#     omp_pattern = re.compile(r"#pragma omp.*")

#     # Walk through the source directory
#     for root, _, files in os.walk(source_dir):
#         for file in files:
#             if file.endswith(".c") or file.endswith(".cpp"):
#                 # Full path to the source file
#                 source_file_path = os.path.join(root, file)

#                 # Read the file content
#                 with open(source_file_path, 'r') as source_file:
#                     content = source_file.read()

#                 # Replace the entire OpenMP pragma line with #pragma drd
#                 modified_content = omp_pattern.sub("#pragma drd", content)

#                 # Construct the destination file path
#                 relative_path = os.path.relpath(root, source_dir)
#                 dest_file_dir = os.path.join(dest_dir, relative_path)
#                 os.makedirs(dest_file_dir, exist_ok=True)
#                 dest_file_path = os.path.join(dest_file_dir, file)

#                 # Write the modified content to the destination file
#                 with open(dest_file_path, 'w') as dest_file:
#                     dest_file.write(modified_content)

#                 print(f"Processed: {source_file_path} -> {dest_file_path}")

# # Example usage
# source_directory = "/programming/dataracebench/micro-benchmarks"
# destination_directory = "/programming/bench"
# replace_omp_pragmas(source_directory, destination_directory)

# import os
# import re

# def delete_files_with_multiple_pragmas(source_dir):
#     """
#     Find and delete all `.c` and `.cpp` files in the source directory that contain at least two `#pragma drd` directives.

#     Args:
#         source_dir (str): Path to the directory containing the source files.
#     """
#     # Regular expression to match `#pragma drd`
#     pragma_pattern = re.compile(r"#pragma drd")

#     # Walk through the source directory
#     for root, _, files in os.walk(source_dir):
#         for file in files:
#             if file.endswith(".c") or file.endswith(".cpp"):
#                 # Full path to the source file
#                 source_file_path = os.path.join(root, file)

#                 # Read the file content
#                 with open(source_file_path, 'r') as source_file:
#                     content = source_file.read()

#                 # Count occurrences of `#pragma drd`
#                 pragma_count = len(pragma_pattern.findall(content))

#                 if pragma_count >= 2:
#                     # Delete the file
#                     os.remove(source_file_path)
#                     print(f"Deleted: {source_file_path}")

# # Example usage
# source_directory = "/programming/bench"
# delete_files_with_multiple_pragmas(source_directory)


# import os
# import shutil

# def copy_common_files(path1, path2, path3):
#     """
#     Copy files with the same name in both `path1` and `path2` to `path3`,
#     taking the files from `path2`.

#     Args:
#         path1 (str): Path to the first directory.
#         path2 (str): Path to the second directory.
#         path3 (str): Path to the destination directory.
#     """
#     # Ensure the destination directory exists
#     os.makedirs(path3, exist_ok=True)

#     # Get the set of file names in path1 and path2
#     files_in_path1 = {f for f in os.listdir(path1) if f.endswith(".c") or f.endswith(".cpp")}
#     files_in_path2 = {f for f in os.listdir(path2) if f.endswith(".c") or f.endswith(".cpp")}

#     # Find common files between the two paths
#     common_files = files_in_path1.intersection(files_in_path2)

#     # Copy common files from path2 to path3
#     for file_name in common_files:
#         src_file = os.path.join(path2, file_name)
#         dest_file = os.path.join(path3, file_name)
#         shutil.copy2(src_file, dest_file)
#         print(f"Copied: {src_file} -> {dest_file}")

# # Example usage
# path1 = "/programming/bench-drd"
# path2 = "/programming/dataracebench/micro-benchmarks"
# path3 = "/programming/subsetParallel"
# copy_common_files(path1, path2, path3)


import os
import subprocess
import csv

# def run_sh_and_log_results(c_path, sh_script, output_csv):
#     """
#     Run `./run.sh` for each `.c` file in a directory and log the results to a CSV.

#     Args:
#         c_path (str): Path containing `.c` files.
#         sh_script (str): Path to the `run.sh` script.
#         output_csv (str): Path to the output CSV file.
#     """
#     # Ensure the output directory for the CSV exists
#     os.makedirs(os.path.dirname(output_csv), exist_ok=True)

#     # List all `.c` files in the directory
#     c_files = [os.path.join(c_path, f) for f in os.listdir(c_path) if f.endswith('.c')]

#     # Open CSV file for writing results
#     with open(output_csv, mode='w', newline='') as csv_file:
#         csv_writer = csv.writer(csv_file)
#         csv_writer.writerow(["Input File", "Result"])

#         # Process each `.c` file
#         for c_file in c_files:
#             try:
#                 # Run the shell script
#                 result = subprocess.run([sh_script, "-i", c_file, "-o", "test2.c"],
#                                         stdout=subprocess.PIPE,
#                                         stderr=subprocess.PIPE,
#                                         text=True)

#                 # Combine stdout and stderr to capture all output
#                 combined_output = result.stdout + result.stderr

#                 # Parse the output
#                 if "seems like data race(waw/raw/war) exists within the loop!" in combined_output:
#                     csv_writer.writerow([c_file, "true"])
#                 elif "seems like no data race exists (please double check)" in combined_output:
#                     csv_writer.writerow([c_file, "false"])
#                 else:
#                     csv_writer.writerow([c_file, "fail"])

#                 print(f"Processed: {c_file}")
#                 result.stdout = ""
#                 result.stderr = ""

#             except Exception as e:
#                 # Handle any unexpected errors
#                 print(f"Error processing {c_file}: {e}")
#                 csv_writer.writerow([c_file, "fail"])




# # Example usage
# c_files_path = "/programming/bench-drd"
# run_sh_script = "./run.sh"
# output_csv_path = "./drsBench.csv"

# run_sh_and_log_results(c_files_path, run_sh_script, output_csv_path)



# with open("drsBench.csv",'r') as f:
#     tp = 0
#     fp = 0
#     tn = 0
#     fn = 0
#     fails = 0
#     counter = 0
#     yes = 0
#     no = 0
#     for r in f:
#         if counter != 0:
#             cols = r.split(",")
#             if "simd" in cols[0]:
#                 continue

#             if "yes" in cols[0] and "true" in cols[1]:
#                 yes +=1
#                 tp += 1
#             elif "no" in cols[0] and "true" in cols[1]:
#                 no += 1
#                 fp += 1
#             elif "no" in cols[0] and "false" in cols[1]:
#                 no += 1
#                 tn += 1
#             elif "yes" in cols[0] and "false" in cols[1]:
#                 yes +=1
#                 fn += 1
#             else:
#                 fails += 1
#         counter += 1
#     print(f"true positives {tp}")
#     print(f"false positives {fp}")
#     print(f"true negatives {tn}")
#     print(f"false negatives {fn}")
#     print(f"fails {fails}")
#     print(f"yes {yes}")
#     print(f"no {no}")
#     print(f"# files {counter-1}")

with open("LLOVBench.csv",'r') as f:
    tp = 0
    fp = 0
    tn = 0
    fn = 0
    fails = 0
    counter = 0
    yes = 0
    no = 0
    for r in f:
        if counter != 0:
            cols = r.split(",")
            if "simd" in cols[0]:
                continue

            if "yes" in cols[0] and "true" in cols[1]:
                yes +=1
                tp += 1
            elif "no" in cols[0] and "true" in cols[1]:
                no += 1
                fp += 1
            elif "no" in cols[0] and "false" in cols[1]:
                no += 1
                tn += 1
            elif "yes" in cols[0] and "false" in cols[1]:
                yes +=1
                fn += 1
            else:
                fails += 1
        counter += 1
    print(f"true positives {tp}")
    print(f"false positives {fp}")
    print(f"true negatives {tn}")
    print(f"false negatives {fn}")
    print(f"fails {fails}")
    print(f"yes {yes}")
    print(f"no {no}")
    print(f"# files {counter-1}")

# with open("openrace.csv",'r') as f:
#     tp = 0
#     fp = 0
#     tn = 0
#     fn = 0
#     fails = 0
#     counter = 0
#     yes = 0
#     no = 0
#     for r in f:
#         if counter != 0:
#             cols = r.split(",")
#             if "simd" in cols[2]:
#                 continue

#             if "yes" in cols[2] and "true" in cols[3]:
#                 yes +=1
#                 tp += 1
#             elif "no" in cols[2] and "true" in cols[3]:
#                 no += 1
#                 fp += 1
#             elif "no" in cols[2] and "false" in cols[3]:
#                 no += 1
#                 tn += 1
#             elif "yes" in cols[2] and "false" in cols[3]:
#                 yes +=1
#                 fn += 1
#             else:
#                 fails += 1
#         counter += 1
#     print(f"true positives {tp}")
#     print(f"false positives {fp}")
#     print(f"true negatives {tn}")
#     print(f"false negatives {fn}")
#     print(f"fails {fails}")
#     print(f"yes {yes}")
#     print(f"no {no}")
#     print(f"# files {counter-1}")