import json
problems = []
with open('minif2f_train.jsonl', 'r', encoding='utf-8') as f:
    for line in f:
        problems.append(json.loads(line))

formal_statement = f"""
{problems[0].get('formal_statement')}  sorry
""".strip()
print(formal_statement)