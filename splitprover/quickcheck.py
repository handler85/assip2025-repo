from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
torch.manual_seed(30)

model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"  # or DeepSeek-Prover-V2-671B
tokenizer = AutoTokenizer.from_pretrained(model_id)


prompt = """
[INST]
Provide a detailed, step-by-step natural language proof plan, followed by the complete Lean 4 proof for the theorem.

Theorem:
/-- Suppose that the roots of the polynomial $P(x)=x^3+ax^2+bx+c$ are $\cos \frac{2\pi}7,\cos \frac{4\pi}7,$ and $\cos \frac{6\pi}7$, where angles are in radians. What is $abc$?

$\textbf{(A) }{-}\frac{3}{49} \qquad \textbf{(B) }{-}\frac{1}{28} \qquad \textbf{(C) }\frac{\sqrt[3]7}{64} \qquad \textbf{(D) }\frac{1}{32}\qquad \textbf{(E) }\frac{1}{28}$ Show that it is $\textbf{(D) }\frac{1}{32}.-/

Proof Plan:
The goal is to find the product `abc` by identifying the coefficients of the monic polynomial `x³ + ax² + bx + c` whose roots are `cos(2π/7)`, `cos(4π/7)`, and `cos(6π/7)`.

1.  **Use the Minimal Polynomial of `2cos(2π/n)`:** The key insight is to use the known minimal polynomial for the algebraic integer `y_k = 2cos(2kπ/7)`. The minimal polynomial whose roots are `2cos(2π/7)`, `2cos(4π/7)`, and `2cos(6π/7)` is `y³ + y² - 2y - 1 = 0`.

2.  **Transform the Polynomial:** We need the polynomial for `x = cos(2kπ/7)`. We can obtain this by substituting `y = 2x` into the minimal polynomial from Step 1.
    `(2x)³ + (2x)² - 2(2x) - 1 = 0`

3.  **Simplify and Normalize:** Expand the transformed polynomial:
    `8x³ + 4x² - 4x - 1 = 0`.
    To match the form `x³ + ax² + bx + c`, we must make it monic by dividing the entire equation by 8.
    `x³ + (4/8)x² - (4/8)x - 1/8 = 0`
    `x³ + (1/2)x² - (1/2)x - 1/8 = 0`

4.  **Identify Coefficients:** By directly comparing the coefficients of our derived polynomial with `x³ + ax² + bx + c = 0`, we can identify `a`, `b`, and `c`.
    *   `a = 1/2`
    *   `b = -1/2`
    *   `c = -1/8`

5.  **Calculate the Final Product:** Compute the product `a * b * c`.
    `abc = (1/2) * (-1/2) * (-1/8) = 1/32`.

Complete Lean 4 Proof:
theorem amc12a_2021_p22 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 3 + a * x ^ 2 + b * x + c)
    (h₁ :
      f⁻¹' {0} =
        {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) :
    a * b * c = 1 / 32 := by
[ASSISTANT]
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