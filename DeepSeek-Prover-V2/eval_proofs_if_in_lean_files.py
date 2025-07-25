import os
import subprocess
import json
import argparse
from typing import List, Dict, Any
from tqdm import tqdm
from pathlib import Path

def process_lean_file(file_path: str, lean_cmd: str, exec_path: str, timeout: int) -> Dict[str, Any]:
    
    problem_name = os.path.splitext(os.path.basename(file_path))[0]
    
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

    try:
        process = subprocess.run(
            ['lake', 'env', 'lean', file_path],
            capture_output=True,
            text=True,
            check=False,
            cwd=exec_path,
            timeout=timeout
        )

        if process.returncode == 0:
            anchor_line = "open BigOperators Real Nat Topology Rat"
            
            anchor_pos = proof_content.find(anchor_line)

            is_commented_out = False
            if anchor_pos != -1:
                text_after_anchor = proof_content[anchor_pos + len(anchor_line):]
                
                if text_after_anchor.strip().startswith('/-') and proof_content.strip().endswith('-/'):
                    is_commented_out = True

            if is_commented_out:
                status = "failed"
                error_message = "Error: No proof generated (stuck in repetitive loop)"
            else:
                status = "success"
                error_message = ""
        else:
            status = "failed"
            error_message = (process.stdout + process.stderr).strip()

    except FileNotFoundError:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean command '{lean_cmd}' not found. Please ensure Lean is installed and in your system's PATH.",
            "generated_proof": proof_content
        }
    except subprocess.TimeoutExpired:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean compilation timed out after {timeout} seconds.",
            "generated_proof": proof_content
        }

    return {
        "problem_name": problem_name,
        "status": status,
        "error_message": error_message,
        "generated_proof": proof_content
    }

def main():

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

    lean_files = [f for f in os.listdir(args.input_dir) if f.endswith('.lean')]

    if not lean_files:
        print(f"No .lean files found in '{args.input_dir}'.")
        return

    all_results = []
    print(f"Found {len(lean_files)} .lean files to process...")
    #exec_path hardcoded
    EXEC_PATH = './minif2f-deepseek'
    if not os.path.isdir(EXEC_PATH):
        print(f"Error: Execution directory '{EXEC_PATH}' not found. Please ensure it exists and is a valid Lean project.")
        return
        
    for filename in tqdm(lean_files, desc="Compiling Lean files"):
        file_path = os.path.join(args.input_dir, filename)
        result = process_lean_file(file_path, args.lean_cmd, EXEC_PATH, args.timeout)
        all_results.append(result)

    try:
        with open(args.output_file, 'w', encoding='utf-8') as f:
            json.dump(all_results, f, indent=4, ensure_ascii=False)
        print(f"\nSuccessfully processed {len(all_results)} files.")
        print(f"Results have been saved to '{args.output_file}'")
    except IOError as e:
        print(f"\nError writing to output file '{args.output_file}': {e}")


if __name__ == "__main__":
    main()