import re

concepts = ["turing_machine", "recursive_function", "bqp", "homotopy_type_theory", "dynamic_programming", "quantum_entanglement", "type_system", "proof_assistant"]
pattern = re.compile(r'- id: "(' + '|'.join(concepts) + r')"')

with open('docs/知识图谱/concept_nodes.yaml', 'r', encoding='utf-8') as f:
    for i, line in enumerate(f, 1):
        if pattern.search(line):
            print(f'{i}: {line.strip()}')
