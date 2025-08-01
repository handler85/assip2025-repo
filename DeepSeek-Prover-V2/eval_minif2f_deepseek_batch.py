import json
from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
import time

torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B" 
json_file_path = "minif2f_train.jsonl" 
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

BATCH_SIZE = 4  
USE_TRUE_BATCHING = True 

def process_batch(batch_problems, batch_start_idx):
    batch_results = []
    
    if not USE_TRUE_BATCHING or len(batch_problems) == 1:
        for i, problem in enumerate(batch_problems):
            result = process_single_problem(problem, batch_start_idx + i)
            batch_results.append(result)
    else:
        try:
            formal_statements = [create_formal_statement(p) for p in batch_problems]
            
            all_chats = []
            for formal_statement in formal_statements:
                chat = [{"role": "user", "content": prompt_template.format(formal_statement)}]
                all_chats.append(chat)
            
            all_inputs = []
            for chat in all_chats:
                inputs = tokenizer.apply_chat_template(
                    chat, tokenize=True, add_generation_prompt=True, return_tensors="pt"
                )
                all_inputs.append(inputs.squeeze(0))  
            
            max_length = max(inp.shape[0] for inp in all_inputs)
            padded_inputs = []
            attention_masks = []
            
            for inp in all_inputs:
                pad_length = max_length - inp.shape[0]
                padded_inp = torch.cat([
                    torch.full((pad_length,), tokenizer.pad_token_id, dtype=inp.dtype),
                    inp
                ])
                padded_inputs.append(padded_inp)
                
                attention_mask = torch.cat([
                    torch.zeros(pad_length, dtype=torch.long),
                    torch.ones(inp.shape[0], dtype=torch.long)
                ])
                attention_masks.append(attention_mask)
            
            device = next(model.parameters()).device
            batch_inputs = torch.stack(padded_inputs).to(device)
            batch_attention_masks = torch.stack(attention_masks).to(device)
            
            print(f"  Processing batch of {len(batch_problems)} problems simultaneously...")
            
            start_time = time.time()
            with torch.no_grad():
                batch_outputs = model.generate(
                    batch_inputs,
                    attention_mask=batch_attention_masks,
                    max_new_tokens=8192,
                    #do_sample=True,
                    #temperature=0.7,
                    pad_token_id=tokenizer.eos_token_id
                )
            generation_time = time.time() - start_time
            
            for i, (problem, inputs, outputs) in enumerate(zip(batch_problems, all_inputs, batch_outputs)):
                generated_text = tokenizer.decode(outputs, skip_special_tokens=True)
                input_text = tokenizer.decode(inputs, skip_special_tokens=True)
                generated_proof = generated_text[len(input_text):].strip()
                
                result = {
                    "problem_name": problem['name'],
                    "informal_prefix": problem.get('informal_prefix'),
                    "formal_statement_with_imports": problem.get('formal_statement'),
                    "generated_proof": generated_proof,
                    "generation_time": generation_time / len(batch_problems),  # Approximate per-problem time
                    "batch_generation_time": generation_time,
                    "batch_size": len(batch_problems),
                    "success": True
                }
                batch_results.append(result)
                print(f"Generated proof for {problem['name']} (batch {batch_start_idx//BATCH_SIZE + 1})")
                
        except Exception as e:
            print(f"Batch processing failed, falling back to sequential: {str(e)}")
            # Fall back to sequential processing
            for i, problem in enumerate(batch_problems):
                result = process_single_problem(problem, batch_start_idx + i)
                batch_results.append(result)
    
    return batch_results

def process_single_problem(problem, problem_idx):
    try:
        print(f"  Processing problem {problem_idx + 1}: {problem['name']}")
        
        formal_statement = create_formal_statement(problem)
        
        chat = [{"role": "user", "content": prompt_template.format(formal_statement)}]
        
        device = next(model.parameters()).device
        inputs = tokenizer.apply_chat_template(
            chat, tokenize=True, add_generation_prompt=True, return_tensors="pt"
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
        
        print(f"Generated proof for {problem['name']} in {generation_time:.2f}s")
        return result
        
    except Exception as e:
        print(f"Error processing {problem['name']}: {str(e)}")
        return {
            "problem_name": problem['name'],
            "formal_statement_with_imports": problem.get('formal_statement'),
            "error": str(e),
            "success": False
        }

for batch_start in range(0, len(problems), BATCH_SIZE):
    batch_end = min(batch_start + BATCH_SIZE, len(problems))
    batch_problems = problems[batch_start:batch_end]
    
    print(f"\nProcessing batch {batch_start//BATCH_SIZE + 1}/{(len(problems)-1)//BATCH_SIZE + 1} "
          f"(problems {batch_start + 1}-{batch_end})")
    
    batch_results = process_batch(batch_problems, batch_start)
    results.extend(batch_results)
    
    for result in batch_results:
        if result.get('success', False):
            total_time += result.get('generation_time', 0)
        
    if (batch_end) % (BATCH_SIZE * 3) == 0 or batch_end == len(problems):
        print(f"\nSaving intermediate results after {batch_end} problems...")
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