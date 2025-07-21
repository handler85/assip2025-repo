import json
from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
import time

torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B" 
json_file_path = "MiniF2F_test_Lean4.json" 
output_file_path = "deepseek_generated_proofs.json"  

print("Loading model and tokenizer...")
tokenizer = AutoTokenizer.from_pretrained(model_id)
model = AutoModelForCausalLM.from_pretrained(
    model_id, 
    device_map="auto", 
    torch_dtype=torch.bfloat16, 
    trust_remote_code=True
)
print("Model loaded successfully!")

with open(json_file_path, 'r', encoding='utf-8') as f:
    problems = json.load(f)

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

# Function to create formal statement from problem data
def create_formal_statement(problem):
    formal_statement = f"""
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

/-- {problem.get('Informal_statement', 'No informal statement provided')} -/
{problem['Statement']} by
  sorry
""".strip()
    return formal_statement

# Results storage
results = []
total_time = 0

# Process each problem
for i, problem in enumerate(problems[160:], start=160):
    print(f"\nProcessing problem {i+1}/{len(problems)}: {problem['Name']}")
    
    try:
        # Create formal statement
        formal_statement = create_formal_statement(problem)
        
        # Create chat prompt
        chat = [
            {"role": "user", "content": prompt_template.format(formal_statement)},
        ]
        
        # Tokenize input
        device = next(model.parameters()).device
        inputs = tokenizer.apply_chat_template(
            chat, 
            tokenize=True, 
            add_generation_prompt=True, 
            return_tensors="pt"
        ).to(device)
        
        # Generate proof
        start_time = time.time()
        print(model.device, device)
        with torch.no_grad():  # Save memory
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
        
        # Extract just the generated part (remove the input prompt)
        input_text = tokenizer.batch_decode(inputs, skip_special_tokens=True)[0]
        generated_proof = generated_text[len(input_text):].strip()
        
        # Store results
        result = {
            "problem_name": problem['Name'],
            "original_statement": problem['Statement'],
            "informal_statement": problem.get('Informal_statement', ''),
            "informal_proof": problem.get('Informal_proof', ''),
            "formal_statement_with_imports": formal_statement,
            "generated_proof": generated_proof,
            "generation_time": generation_time,
            "success": True
        }
        
        results.append(result)
        print(f"Generated proof for {problem['Name']} in {generation_time:.2f}s")
        
        # Optionally print a preview of the generated proof
        print("Generated proof preview:")
        print(generated_proof[:200] + "..." if len(generated_proof) > 200 else generated_proof)
        
    except Exception as e:
        print(f"Error processing {problem['Name']}: {str(e)}")
        result = {
            "problem_name": problem['Name'],
            "original_statement": problem['Statement'],
            "error": str(e),
            "success": False
        }
        results.append(result)
    
    # Save intermediate results periodically (every 10 problems)
    if (i + 1) % 10 == 0:
        print(f"\nSaving intermediate results after {i + 1} problems...")
        with open(f"intermediate_{output_file_path}", 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)

# Save final results
print(f"\nSaving all results to {output_file_path}...")
with open(output_file_path, 'w', encoding='utf-8') as f:
    json.dump(results, f, indent=2, ensure_ascii=False)

# Print summary statistics
successful = sum(1 for r in results if r.get('success', False))
print(f"\n=== SUMMARY ===")
print(f"Total problems processed: {len(problems)}")
print(f"Successful generations: {successful}")
print(f"Failed generations: {len(problems) - successful}")
print(f"Total time: {total_time:.2f}s")
print(f"Average time per problem: {total_time/len(problems):.2f}s")
print(f"Results saved to: {output_file_path}")