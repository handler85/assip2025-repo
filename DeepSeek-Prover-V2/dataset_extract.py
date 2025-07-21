from datasets import load_dataset
ds = load_dataset("AI-MO/minif2f_test")
for split, dataset in ds.items():
    dataset.to_json(f"minif2f_{split}.jsonl")