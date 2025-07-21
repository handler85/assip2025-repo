import json
import os
import subprocess
from tqdm import tqdm 


INPUT_JSON_PATH = './deepseek_generated_proofs.json' 

OUTPUT_JSON_PATH = './proof_eval_results.json'

LEAN_PROJECT_PATH = './minif2f-deepseek'
LEAN_EXEC_PATH = './minif2f-deepseek'



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
    print(" Done.")

if __name__ == "__main__":
    main()