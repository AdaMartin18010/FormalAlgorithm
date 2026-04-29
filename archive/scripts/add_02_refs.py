with open('docs/05-类型理论/02-依赖类型论.md','r',encoding='utf-8') as f:
    text = f.read()
old = '**引用规范说明 / Citation Guidelines**:'
new = '[45] Cubical Agda Development Team. \"Cubical Agda 0.6 Release\". 2024.\n\n[46] Cubical Team. \"Collapsed Glue Types for Univalence Optimization\". 2024.\n\n[47] SMTCoq Development Team. \"SMTCoq 2.0: Automation for Cubical and Dependent Types\". CPP 2024, 2024.\n\n**引用规范说明 / Citation Guidelines**:'
text = text.replace(old, new)
with open('docs/05-类型理论/02-依赖类型论.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added refs 45-47 to 02')
