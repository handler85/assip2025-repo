import json
import os
import subprocess
from tqdm import tqdm 


INPUT_JSON_PATH = './deepseek_generated_proofs.json' 

OUTPUT_JSON_PATH = './proof_eval_results.json'

LEAN_PROJECT_PATH = './minif2f-deepseek'
LEAN_EXEC_PATH = './minif2f-deepseek'


def evaluate_lean_proof(proof_string, lean_project_path, lean_exec_path, temp_filename="TempProof.lean"):
    """
    Evaluates a single Lean proof string by writing it to a file
    and running the Lean compiler on it.
    """
   
    lean_file_header = "import Mathlib\nimport Aesop\nset_option maxHeartbeats 0\nopen BigOperators Real Nat Topology Rat\n"
    
    # Handle cases where the model might regenerate the theorem statement
    # We only want the proof tactics, so we look for `:= by`
    if ":= by" in proof_string:
        full_lean_code = lean_file_header + proof_string
    else:
        # This is a basic handler; re-add the statement?
        return {"status": "failed", "error_message": "Invalid format: Proof does not contain a ':= by' clause."}
        #full_lean_code = lean_file_header + fl_statement + " by" + "\n" + proof_string


    temp_file_path = os.path.join(lean_project_path, temp_filename)

    try:
        with open(temp_file_path, 'w', encoding='utf-8') as f:
            f.write(full_lean_code)

        result = subprocess.run(
            ['lake', 'env', 'lean', temp_filename],
            capture_output=True,
            text=True,
            cwd=lean_exec_path, 
            timeout=60 
        )

        error_message = result.stdout + result.stderr

        if result.returncode == 0 and "unsolved goals" not in error_message:
            return {"status": "success", "error_message": ""}
        else:
            if "unsolved goals" in error_message:
                return {"status": "failed", "error_message": "Unsolved goals remaining."}
            return {"status": "failed", "error_message": error_message.strip()}

    except subprocess.TimeoutExpired:
        return {"status": "failed", "error_message": "Timeout: Proof compilation took too long."}
    except Exception as e:
        return {"status": "failed", "error_message": f"An unexpected script error occurred: {e}"}
    finally:
        if os.path.exists(temp_file_path):
            os.remove(temp_file_path)


def main():
   
    print(f"Loading generated proofs from: {INPUT_JSON_PATH}")
    try:
        with open(INPUT_JSON_PATH, 'r', encoding='utf-8') as f:
            all_problems = json.load(f)
    except FileNotFoundError:
        print(f"FATAL: Input file not found at {INPUT_JSON_PATH}. Please check the path.")
        return
    except json.JSONDecodeError:
        print(f"FATAL: Could not parse the JSON file. It might be corrupted.")
        return

    print(f"Found {len(all_problems)} problems to evaluate.")
    
    evaluation_results = []
    
    for problem in tqdm(all_problems, desc="Evaluating Problems"):
        problem_name = problem.get("problem_name")
        generated_proofs = problem.get("generated_proof", [])
        if not generated_proofs:
            continue 

        for i, proof_attempt in enumerate(generated_proofs):
            evaluation = evaluate_lean_proof(proof_attempt, LEAN_PROJECT_PATH, LEAN_EXEC_PATH)
            
            result_record = {
                "problem_name": problem_name,
                "attempt_index": i,
                "status": evaluation["status"],
                "error_message": evaluation["error_message"],
                "generated_proof": proof_attempt # Keep the original proof for reference
            }
            evaluation_results.append(result_record)

    print(f"\nEvaluation complete. Saving {len(evaluation_results)} results to: {OUTPUT_JSON_PATH}")
    
    with open(OUTPUT_JSON_PATH, 'w', encoding='utf-8') as f:
        json.dump(evaluation_results, f, indent=4)

    print(" Done.")

if __name__ == "__main__":
    main()