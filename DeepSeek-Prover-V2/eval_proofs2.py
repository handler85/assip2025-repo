import os
import subprocess
import json
import argparse
from typing import List, Dict, Any
from tqdm import tqdm

def process_lean_file(file_path: str, lean_cmd: str, exec_path: str, timeout: int) -> Dict[str, Any]:
    """
    Processes a single .lean file: reads its content, runs the Lean compiler,
    and captures the result.

    Args:
        file_path (str): The full path to the .lean file.
        lean_cmd (str): The command to execute the Lean compiler.
        timeout (int): Timeout in seconds for the lean process.

    Returns:
        A dictionary containing the processing result.
    """
    problem_name = os.path.splitext(os.path.basename(file_path))[0]
    
    # 1. Read the content of the .lean file
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            proof_content = f.read()
    except IOError as e:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Error reading file: {e}",
            "generated_proof": ""
        }

    # 2. Run the Lean compiler on the file
    try:
        # We use subprocess.run to execute the 'lean' command.
        # - `capture_output=True`: Captures stdout and stderr.
        # - `text=True`: Decodes stdout/stderr as text.
        # - `check=False`: Prevents raising an exception on non-zero exit codes.
        # - `timeout`: Prevents the script from hanging on a complex proof.
        process = subprocess.run(
            [lean_cmd, file_path],
            capture_output=True,
            text=True,
            check=False,
            cwd=exec_path,
            timeout=timeout
        )

        # 3. Determine the status based on the compiler's exit code
        if process.returncode == 0:
            # Success: exit code 0 means no errors.
            status = "success"
            # Lean often prints to stdout even on success, so we clear the error message.
            error_message = ""
        else:
            # Failure: any other exit code indicates an error.
            status = "failed"
            # The error message from Lean is usually printed to stderr.
            # Sometimes there's relevant info in stdout too, so we combine them.
            error_message = (process.stdout + process.stderr).strip()

    except FileNotFoundError:
        # This error occurs if the 'lean' command itself is not found.
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean command '{lean_cmd}' not found. Please ensure Lean is installed and in your system's PATH.",
            "generated_proof": proof_content
        }
    except subprocess.TimeoutExpired:
        # This error occurs if the process takes too long.
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean compilation timed out after {timeout} seconds.",
            "generated_proof": proof_content
        }

    # 4. Assemble the final result dictionary for this file
    return {
        "problem_name": problem_name,
        "status": status,
        "error_message": error_message,
        "generated_proof": proof_content
    }

def main():
    """
    Main function to parse arguments and orchestrate the processing of .lean files.
    """
    parser = argparse.ArgumentParser(
        description="Run the Lean compiler on a directory of .lean files and record the results in a JSON file.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument(
        "input_dir",
        help="The directory containing the .lean files to process."
    )
    parser.add_argument(
        "output_file",
        help="The path to the output JSON file where results will be saved."
    )
    parser.add_argument(
        "--lean_cmd",
        default="lake env lean",
        help="The command to run the Lean 4 compiler (e.g., '/path/to/lean' or just 'lean' if in PATH).\nDefault: 'lean'"
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Timeout in seconds for compiling a single Lean file.\nDefault: 60"
    )

    args = parser.parse_args()

    if not os.path.isdir(args.input_dir):
        print(f"Error: Input directory '{args.input_dir}' not found.")
        return

    # Find all .lean files in the specified directory
    lean_files = [f for f in os.listdir(args.input_dir) if f.endswith('.lean')]

    if not lean_files:
        print(f"No .lean files found in '{args.input_dir}'.")
        return

    all_results = []
    print(f"Found {len(lean_files)} .lean files to process...")
    EXEC_PATH = './minif2f-deepseek'
    # Process each file with a progress bar
    for filename in tqdm(lean_files, desc="Compiling Lean files"):
        file_path = os.path.join(args.input_dir, filename)
        result = process_lean_file(file_path, args.lean_cmd, EXEC_PATH, args.timeout)
        all_results.append(result)

    # Write the collected results to the output JSON file
    try:
        with open(args.output_file, 'w', encoding='utf-8') as f:
            # `indent=4` makes the JSON file human-readable
            json.dump(all_results, f, indent=4, ensure_ascii=False)
        print(f"\nSuccessfully processed {len(all_results)} files.")
        print(f"Results have been saved to '{args.output_file}'")
    except IOError as e:
        print(f"\nError writing to output file '{args.output_file}': {e}")


if __name__ == "__main__":
    main()