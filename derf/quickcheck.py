from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"  # or DeepSeek-Prover-V2-671B
tokenizer = AutoTokenizer.from_pretrained(model_id)


prompt = """
The following Lean 4 proof is incorrect:
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  have h_main : S.card = 100 := by
    have : S = Finset.filter (fun n => n % 10 = 0) (Finset.filter (fun n => (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d)) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))) := by
      apply Finset.ext
      intro n
      simp only [Finset.mem_filter, Finset.mem_Icc, h₀, Nat.mod_eq_of_lt]
      <;>
      (try omega) <;>
      (try
        {
          constructor <;> intro h <;>
          (try simp_all [Nat.even_iff, Nat.odd_iff, Nat.mod_eq_of_lt]) <;>
          (try omega) <;>
          (try omega) <;>
          (try omega)
        }) <;>
      (try
        {
          aesop
        }) <;>
      (try
        {
          norm_num at * <;>
          omega
        })
    rw [this]
    rfl
  exact h_main

The proof above throws the following error when compiled by Lean 4:
/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:61:32: error: unsolved goals\ncase this\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\n⊢ S =\n    Finset.filter (fun n => n % 10 = 0)\n      (Finset.filter (fun n => ∀ d ∈ digits 10 n, Even d) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))\n\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\nthis :\n  S =\n    Finset.filter (fun n => n % 10 = 0)\n      (Finset.filter (fun n => ∀ d ∈ digits 10 n, Even d) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))\n⊢ S.card = 100\n/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:60:20: error: unsolved goals\nS : Finset ℕ\nh₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d ∈ digits 10 n, Even d) ∧ 5 ∣ n\nh_main : S.card = 100\n⊢ S.card = 100\n/root/assip2025-repo/DeepSeek-Prover-V2/deepseek-proofs/DeepseekProofs/amc12a_2020_p4.lean:62:177: error: unexpected token ')'; expected command
This is the result of a logic translation error - your NL reasoning was excellent, but you failed to translate it into a valid proof strategy.
Complete the following Lean 4 code:
```lean4
theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  sorry
```
Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies, MAKING SURE TO FIX THE ERROR MADE ABOVE.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()

chat = [
  {"role": "user", "content": prompt},
]

model = AutoModelForCausalLM.from_pretrained(
    model_id, 
    device_map="auto", 
    torch_dtype=torch.bfloat16, 
    trust_remote_code=True
)


device = next(model.parameters()).device
inputs = tokenizer.apply_chat_template(
    chat, 
    tokenize=True, 
    add_generation_prompt=True, 
    return_tensors="pt"
).to(device)
print(model.device, device)

import time
start = time.time()
with torch.no_grad():  
    outputs = model.generate(
        inputs, 
        max_new_tokens=8192,
        #do_sample=True,  
        #temperature=0.7,
        pad_token_id=tokenizer.eos_token_id
    )
print(tokenizer.batch_decode(outputs))
print(time.time() - start)