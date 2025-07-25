import json
import os
import argparse

def extract_proofs_to_lean_files(input_json_path, output_directory):
   
    if not os.path.exists(input_json_path):
        print(f"Error: Input file not found at '{input_json_path}'")
        return

    try:
        os.makedirs(output_directory, exist_ok=True)
        print(f"Output will be saved in '{os.path.abspath(output_directory)}'")
    except OSError as e:
        print(f"Error: Could not create output directory '{output_directory}'. {e}")
        return

    try:
        with open(input_json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except json.JSONDecodeError:
        print(f"Error: Could not decode JSON from '{input_json_path}'. The file may be malformed.")
        return
    except Exception as e:
        print(f"An unexpected error occurred while reading the file: {e}")
        return

    if not isinstance(data, list):
        print(f"Error: The JSON file does not contain a list of entries. Expected format: [{{...}}, {{...}}]")
        return

    proof_count = 0
    for i, entry in enumerate(data):
        if not isinstance(entry, dict):
            print(f"Warning: Item at index {i} is not a JSON object (dictionary). Skipping.")
            continue

        proof_text = entry.get("generated_proof")
        problem_name = entry.get("problem_name")
        if proof_text is None:
            print(f"Warning: 'generated_proof' key not found in entry at index {i}. Skipping.")
            continue

        if not isinstance(proof_text, str):
            print(f"Warning: Value for 'generated_proof' at index {i} is not a string. Skipping.")
            continue
            
        output_filename = f"{problem_name}.lean"
        output_filepath = os.path.join(output_directory, output_filename)

        try:
            with open(output_filepath, 'w', encoding='utf-8') as out_file:
                out_file.write("import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n")
                out_file.write(proof_text)
            print(f"  - Successfully wrote proof from entry {i} to '{output_filepath}'")
            proof_count += 1
        except IOError as e:
            print(f"Error: Could not write to file '{output_filepath}'. {e}")

    print(f"\nExtraction complete. Wrote {proof_count} proof(s).")

def main():
    parser = argparse.ArgumentParser(
        description="Extracts 'generated_proof' from each entry in a JSON list and saves them as individual .lean files.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    
    parser.add_argument(
        "input_file",
        help="The path to the input JSON file (which should contain a list of objects)."
    )
    
    parser.add_argument(
        "-o", "--output-dir",
        default="extracted_ds_proofs",
        help="The directory to save the .lean files into.\n(default: 'extracted_ds_proofs')"
    )
    
    args = parser.parse_args()
    
    extract_proofs_to_lean_files(args.input_file, args.output_dir)

if __name__ == "__main__":
    main()