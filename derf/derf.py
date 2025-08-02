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
torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B" 
json_file_path = "test_prob.jsonl" 
output_file_path = "deepseek_derf_generated_proofs.json"  
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



def process_lean_file(file_path: Path):
   
    print(f"--- Checking: {file_path.name}")

    try:
        original_content = file_path.read_text(encoding='utf-8')

        trigger_sequence = "### Complete Lean 4 Proof\n\n```lean4"
        if trigger_sequence not in original_content:
            print("    -> Skipping: Required trigger sequence not found.")
            return

        print("    -> Found trigger sequence. Preparing modifications...")

        modified_content = original_content

        detailed_statement = "### Detailed"
        if detailed_statement in modified_content:
            modified_content = modified_content.replace(
                detailed_statement,
                f"/- {detailed_statement}",
                1
            )
            print("    - Action: Added '/-' before '### Detailed'.")
        else:
            print("    - Warning: '### Detailed' not found, skipping this action.")


       
        replacement_sequence = "### Complete Lean 4 Proof\n\nlean4\n-/"
        if trigger_sequence in modified_content:
            modified_content = modified_content.replace(
                trigger_sequence,
                replacement_sequence,
                1
            )
            print("    - Action: Modified the 'Complete Proof' code block and added '-/'.")
        else:
            print("    - Warning: Trigger sequence disappeared during processing. Aborting modification.")
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
            print("    - Action: Removed the final '```' from the end of the file.")
        else:
            print("    - Warning: Final '```' not found at the end of the file. Skipping this action.")


        
        file_path.write_text(modified_content, encoding='utf-8')
        print("    -> SUCCESS: File has been modified and saved.")

    except Exception as e:
        print(f"    -> ERROR: Could not process file {file_path.name}. Reason: {e}")


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

def eval_lean_file(file_path: str, lean_cmd: str, exec_path: str, timeout: int) -> Dict[str, Any]:
    
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
