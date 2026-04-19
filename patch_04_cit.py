with open('docs/05-类型理论/04-类型系统.md','r',encoding='utf-8') as f:
    text = f.read()
text = text.replace('[Coq8192024]', '[27]')
refs = '[27] The Coq Development Team. \"The Coq Proof Assistant, Version 8.19\". 2024.\n\n'
text = text.replace('## 与项目结构主题的对齐 / Alignment with Project Structure', refs + '## 与项目结构主题的对齐 / Alignment with Project Structure')
with open('docs/05-类型理论/04-类型系统.md','w',encoding='utf-8') as f:
    f.write(text)
print('Patched 04 citations')
