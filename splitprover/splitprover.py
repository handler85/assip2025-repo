#imports

#take problem from .json minif2f
#prompt ds
#receive response
#write to .lean file in lean project with right env
#HAVE BACKUP BEFORE NEXT STEP
#extract proof logic
#eval .lean proof
#take error data, write to .json

#if good, good
#if not, gemini api to classify error into identified categories
#reprompt deepseek in same convo with predetermined prompt for that error type
#repeat

#WRITE IN ALL MISSING PATHS
#figure out gpu cpu (does concurrent work)
#run thru whole code check it

import json
from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
import time
import os
import argparse
from pathlib import Path
import subprocess
from typing import List, Dict, Any
from tqdm import tqdm
import concurrent.futures
import sys
import google.generativeai as genai
torch.manual_seed(42)

MODEL_ID = "deepseek-ai/DeepSeek-Prover-V2-7B" 
PROBLEMS_FILE_PATH = "test_prob.jsonl" 
OUTPUT_FILE_PATH = "deepseek_derf_generated_proofs.json"  
LEAN_PROJECT_PATH = ""
TEMP_LEAN_DIR = os.path.join(LEAN_PROJECT_PATH, "temp_proofs")
MAX_ATTEMPTS_PER_PROBLEM = 5
EVALUATION_TIMEOUT = 120
# export GOOGLE_API_KEY="[key]"
try:
    api_key = os.environ["GOOGLE_API_KEY"]
    genai.configure(api_key=api_key)
except KeyError:
    print("ERROR: GOOGLE_API_KEY environment variable not set.")
    print("Please set the environment variable and try again.")
    sys.exit(1) 

def create_initial_prompt(problem: Dict[str, Any]) -> str:
    formal_statement = f"""
{problem.get('formal_statement')}  sorry
""".strip()
    prompt_template = """
Complete the following Lean 4 code:
```lean4
{}
```
Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()
    return prompt_template.format(formal_statement)
def create_reprompt(error_category: str, failed_proof: str, error_message: str) -> str:
    prompts = {}
    instruction = prompts.get(error_category)
    return f'''
    The previous proof attempt failed.
    Error message:
    {error_message}
    Failed proof code:
    {failed_proof}
    INSTRUCTION: {instruction}
    Please provide the complete, corrected Lean4 proof.
    '''.strip()

def save_and_prepare_lean_file(problem_name: str, proof_text: str, attempt:int) -> Path:
    safe_problem_name = "".join(c for c in problem_name if c.isalnum() or c in ('_', '-')).rstrip()
    filename = f"{safe_problem_name}attempt{attempt}.lean"
    file_path = Path(TEMP_LEAN_DIR) / filename
    os.makedirs(TEMP_LEAN_DIR, exist_ok=True)
    
       
    full_content = f"""
    import Mathlib
    import Aesop
    set_option maxHeartbeats 0
    open BigOperators Real Nat Topology Rat
    
    {proof_text}
    """    
    file_path.write_text(full_content, encoding='utf-8')        
    return file_path

def process_lean_file(file_path: Path):
   
    try:
        original_content = file_path.read_text(encoding='utf-8')

        trigger_sequence = "### Complete Lean 4 Proof\n\n```lean4"
        if trigger_sequence not in original_content:
            return

        modified_content = original_content

        detailed_statement = "### Detailed"
        if detailed_statement in modified_content:
            modified_content = modified_content.replace(
                detailed_statement,
                f"/- {detailed_statement}",
                1
            )

        replacement_sequence = "### Complete Lean 4 Proof\n\nlean4\n-/"
        if trigger_sequence in modified_content:
            modified_content = modified_content.replace(
                trigger_sequence,
                replacement_sequence,
                1
            )
        else:
            return

       
        lines = modified_content.splitlines()
        last_line_index = -1
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip():
                last_line_index = i
                break
        
        if last_line_index != -1 and lines[last_line_index].strip() == "```":
            modified_content = "\n".join(lines[:last_line_index])
            if modified_content:
                modified_content += "\n"
        file_path.write_text(modified_content, encoding='utf-8')

    except Exception as e:
        print(f"    -> ERROR: Could not process file {file_path.name}. Reason: {e}")

def eval_lean_file(file_path: Path) -> Dict[str, Any]:
    
    with open(str(file_path), 'r', encoding='utf-8') as f:
        proof_content = f.read()
    

    try:
        process = subprocess.run(
            ['lake', 'env', 'lean', str(file_path)],
            capture_output=True,
            text=True,
            check=False,
            cwd=LEAN_PROJECT_PATH,
            timeout=EVALUATION_TIMEOUT
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
                return {
                    "status": "failed",
                    "error_message": "Error: No proof generated (stuck in repetitive loop)"
                }
            else:
                return {
                    "status": "success",
                    "error_message": ""
                }
        else:
            error_message = (process.stdout + process.stderr).strip()

            return {
                "status": "failed",
                "error_message": error_message
            }

    except FileNotFoundError:
        return {
            "status": "failed",
            "error_message": "The lake command was not found. Is Lean installed and in your PATH?"
        }
    except subprocess.TimeoutExpired:
        return {
            "status": "failed",
            "error_message": f"Lean compilation timed out after {EVALUATION_TIMEOUT} seconds."
        }
    except Exception as e:
        return {
            "status": "failed",
            "error_message": f"An unexpected error occurred during evaluation: {e}"
        }


def classify_error_with_gemini(problem_name: str, proof: str, error_message: str):
    
    model = genai.GenerativeModel('gemini-pro')

    prompt = f"""
    The following Lean 4 proof attempt for the problem '{problem_name}' failed.

    The error message was: 
    '{error_message}'

    Here is the full generated proof:
    --- FAILED PROOF ---
    {proof}
    --- END FAILED PROOF ---

    Based on the error and the code, classify the primary error into ONE of the following categories:

    T: Timeout: Brute-Force/Inefficient Strategy: The model defaults to computationally expensive tactics like interval_cases on large ranges or nlinarith/omega on goals that are too complex or non-linear for them to solve quickly, often resulting in a timeout or tactic failure. For this error type, the NL proof and Lean proof structure are correct, but the tactics used are inefficient.
    M: Mathematical Error: The model makes a mathematical mistake in its initial NL reasoning (e.g., miscalculation, wrong theorem application), or fails to grasp the correct solution to the problem, which makes the subsequent Lean proof attempt futile.
    L: Repetitive Loop/Generation Failure (subset of M-errors): The model's generation process breaks down, causing it to repeat the same text, calculations, or code snippets endlessly without making progress, failing to produce a complete proof. This is triggered by a mathematical error, but is a distinct behavior exhibited by the model. Errors are classified as M-errors when a genuine proof attempt follows NL reasoning, while L-errors are loops of text that do not lead to a coherent Lean proof attempt.
    S: Syntax and Compilation Errors: The model produces syntactically invalid Lean code (e.g., unexpected tokens, incorrect function calls, malformed expressions) that fails to compile.
    IP: Incorrect Proof Strategy/Logic Translation Failure: The NL proof is correct, but the formal Lean proof strategy is fundamentally wrong to implement the NL proof, and the model fails to translate the sound NL proof into a working Lean proof.
    U: Tactic Failure/Unsolved Goals: The overall proof strategy is plausible, but a specific tactic (linarith, rewrite, rfl, omega) fails because its preconditions are not met, the goal is outside its capabilities, or necessary lemmas are missing.
    
    Respond with ONLY the one or two-letter code for the error type most detrimental to the proof attempt (T, M, L, S, IP, U).
    The last word in your response should be the identified error category code.
    """
    try:
        response = model.generate_content(prompt)
        category = response.text.strip().split()[-1].strip('.,;?!')
        return category
    except Exception as e:
        print(f"WARNING: Gemini API call failed: {e}")
        return None
    
print("Loading model and tokenizer...")
tokenizer = AutoTokenizer.from_pretrained(model_id)
model = AutoModelForCausalLM.from_pretrained(
    model_id, 
    device_map="auto", 
    torch_dtype=torch.bfloat16, 
    trust_remote_code=True
)
print("Model loaded successfully!")

problems = []
with open(json_file_path, 'r', encoding='utf-8') as f:
    for line in f:
        problems.append(json.loads(line))

print(f"Loaded {len(problems)} problems from {json_file_path}")

# Template for the prompt
prompt_template = """
Complete the following Lean 4 code:
```lean4
{}
```
Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()

def create_formal_statement(problem):
    formal_statement = f"""
{problem.get('formal_statement')}  sorry
""".strip()
    return formal_statement

results = []
total_time = 0

for i, problem in enumerate(problems):
    print(f"\nProcessing problem {i+1}/{len(problems)}: {problem['name']}")
    
    try:
        formal_statement = create_formal_statement(problem)
        
        chat = [
            {"role": "user", "content": prompt_template.format(formal_statement)},
        ]
        
        device = next(model.parameters()).device
        inputs = tokenizer.apply_chat_template(
            chat, 
            tokenize=True, 
            add_generation_prompt=True, 
            return_tensors="pt"
        ).to(device)
        
        start_time = time.time()
        print(model.device, device)
        with torch.no_grad():  
            outputs = model.generate(
                inputs, 
                max_new_tokens=8192,
                #do_sample=True,  
                #temperature=0.7,
                pad_token_id=tokenizer.eos_token_id
            )
        generation_time = time.time() - start_time
        total_time += generation_time
        
        generated_text = tokenizer.batch_decode(outputs, skip_special_tokens=True)[0]
        
        input_text = tokenizer.batch_decode(inputs, skip_special_tokens=True)[0]
        generated_proof = generated_text[len(input_text):].strip()
        
        result = {
            "problem_name": problem['name'],
            "informal_prefix": problem.get('informal_prefix'),
            "formal_statement_with_imports": problem.get('formal_statement'),
            "generated_proof": generated_proof,
            "generation_time": generation_time,
            "success": True
        }
        
        results.append(result)
        print(f"Generated proof for {problem['name']} in {generation_time:.2f}s")
        
        print("Generated proof preview:")
        print(generated_proof[:200] + "..." if len(generated_proof) > 200 else generated_proof)
        
    except Exception as e:
        print(f"Error processing {problem['name']}: {str(e)}")
        result = {
            "problem_name": problem['name'],
            "formal_statement_with_imports": problem.get('formal_statement'),
            "error": str(e),
            "success": False
        }
        results.append(result)
    
    if (i + 1) % 10 == 0:
        print(f"\nSaving intermediate results after {i + 1} problems...")
        with open(f"intermediate_{output_file_path}", 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)

print(f"\nSaving all results to {output_file_path}...")
with open(output_file_path, 'w', encoding='utf-8') as f:
    json.dump(results, f, indent=2, ensure_ascii=False)

successful = sum(1 for r in results if r.get('success', False))
print(f"\n=== SUMMARY ===")
print(f"Total problems processed: {len(problems)}")
print(f"Successful generations: {successful}")
print(f"Failed generations: {len(problems) - successful}")
print(f"Total time: {total_time:.2f}s")
print(f"Average time per problem: {total_time/len(problems):.2f}s")
print(f"Results saved to: {output_file_path}")



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



input_json_file = output_file_path
output_dir = 'extracted_ds_derf_proofs'
extract_proofs_to_lean_files(input_json_file, output_dir)





lean_directory = ''



lean_directory = Path(lean_directory)



print(f"Starting script in directory: {lean_directory.resolve()}")



lean_files = list(lean_directory.glob("*.lean"))

        
for file_path in lean_files:
    process_lean_file(file_path)
    print("-" * 20)

    print("Script finished.")


def check_if_already_have(file_path, search_string):
    if not os.path.exists(file_path) or os.path.getsize(file_path) == 0:
        return False
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            if search_string in content:
                return True
            else:
                return False
    except FileNotFoundError:
        return False


input_dir = ''
lean_eval_output_file = ''
lean_cmd = 'lake env lean'
timeout = 120



lean_files = [f for f in os.listdir(input_dir) if f.endswith('.lean')]

    

all_results = []
print(f"Found {len(lean_files)} .lean files to process...")
#exec_path hardcoded
EXEC_PATH = ''
   
num_workers = os.cpu_count()
    
# Use a ProcessPoolExecutor to run compilations in parallel
with concurrent.futures.ProcessPoolExecutor(max_workers=num_workers) as executor:
    # Create a future for each file processing task
    future_to_file = {
        executor.submit(eval_lean_file, os.path.join(input_dir, filename), lean_cmd, EXEC_PATH, timeout): filename 
        for filename in lean_files
    }
    
    # Use tqdm to show progress as tasks complete
    for future in tqdm(concurrent.futures.as_completed(future_to_file), total=len(lean_files), desc="Compiling Lean files"):
        try:
            result = future.result()
            all_results.append(result)
        except Exception as exc:
            filename = future_to_file[future]
            print(f"\nError processing {filename}: {exc}")

try:
    with open(lean_eval_output_file, 'w', encoding='utf-8') as f:
        json.dump(all_results, f, indent=4, ensure_ascii=False)
    print(f"\nSuccessfully processed {len(all_results)} files.")
    print(f"Results have been saved to '{lean_eval_output_file}'")
except IOError as e:
    print(f"\nError writing to output file '{lean_eval_output_file}': {e}")

'''
    for filename in tqdm(lean_files, desc="Compiling Lean files"):
        file_path = os.path.join(args.input_dir, filename)
        
        #if check_if_already_have("deepseek_proofs_eval2.json", f'"{os.path.splitext(os.path.basename(file_path))[0]}"'):
         #   print(f"Found '{os.path.splitext(os.path.basename(file_path))[0]}' in the file. Will not dump new data.")
        
        #else:
            
        result = eval_lean_file(file_path, args.lean_cmd, EXEC_PATH, args.timeout)
        all_results.append(result)
        try:
            with open(lean_eval_output_file, 'w', encoding='utf-8') as f:
                json.dump(all_results, f, indent=4, ensure_ascii=False)
        except IOError as e:
            print(f"\nError writing to output file '{lean_eval_output_file}': {e}")
    try:
        with open(lean_eval_output_file, 'w', encoding='utf-8') as f:
            json.dump(all_results, f, indent=4, ensure_ascii=False)
        print(f"\nSuccessfully processed {len(all_results)} files.")
        print(f"Results have been saved to '{lean_eval_output_file}'")
    except IOError as e:
        print(f"\nError writing to output file '{lean_eval_output_file}': {e}")

'''






def process_json_file(filepath: str):

    if not os.path.exists(filepath):
        print(f"Error: File '{filepath}' not found.")
        return

    print(f"Starting to process file '{filepath}'...\n" + "="*40)

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            all_objects = json.load(f)

        if not isinstance(all_objects, list):
            print("Error: JSON file does not contain a list of objects.")
            print("The file should start with '[' and end with ']'.")
            return

    except json.JSONDecodeError:
        print(f"Error: Could not decode JSON from '{filepath}'. Check for syntax errors.")
        return
    except Exception as e:
        print(f"An unexpected error occurred while reading file '{filepath}': {e}")
        return

    for i, problem_obj in enumerate(all_objects):
        if not isinstance(problem_obj, dict):
            print(f"Warning: Item at index {i} is not a JSON object. Skipping.")
            continue

        problem_name = problem_obj.get("problem_name")
        status = problem_obj.get("status")

        print(f"Processing '{problem_name}' (Object {i+1}/{len(all_objects)})...")

        if status == "success":
            print("  - Status: SUCCESS. Moving to next object.\n")
            continue
        else:
            print(f"  - Status: {status}. Taking action.")
            suggested_fix = call_gemini_for_fix(problem_obj)
            
            if suggested_fix:
                print(f"  -> Gemini's suggested fix (last word): '{suggested_fix}'\n")
            else:
                print("  -> Could not get a suggestion from Gemini.\n")

process_json_file(lean_eval_output_file)