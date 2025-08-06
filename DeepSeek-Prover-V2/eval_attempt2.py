import json
from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
import time

torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B" 
json_file_path = "delete.jsonl" 
output_file_path = "delete_derf_test.json"  
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
Your generated Lean 4 proof failed. You failed to translate your correct NL proof into a valid Lean 4 proof, due to an incorrect Lean 4 proof strategy.
The Lean 4 compiler error message was the following: "/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:61:32: error: unsolved goals\ncase this\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\n⊢ S =\n    Finset.filter (fun n => n % 10 = 0)\n      (Finset.filter (fun n => ∀ d ∈ digits 10 n, Even d) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))\n\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\nthis :\n  S =\n    Finset.filter (fun n => n % 10 = 0)\n      (Finset.filter (fun n => ∀ d ∈ digits 10 n, Even d) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))\n⊢ S.card = 100\n/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:60:20: error: unsolved goals\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\nh_main : S.card = 100\n⊢ S.card = 100\n/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:62:177: error: unexpected token ')'; expected command"

Complete the following Lean 4 code:
```lean4
{}
```
Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies. Correct your error of incorrectly translating your correct NL proof into a valid Lean 4 proof.
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