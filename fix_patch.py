import re

with open("patch_all.py", "r", encoding="utf-8") as f:
    code = f.read()

code = code.replace(
    "text05 = pat23.sub(sec23, text05)",
    "text05 = pat23.sub(lambda m: sec23, text05)"
)

code = code.replace(
    "text05 = pat34.sub(sec34 + \"\\\\n\", text05, count=1)",
    "text05 = pat34.sub(lambda m: sec34 + \"\\n\", text05, count=1)"
)

with open("patch_all.py", "w", encoding="utf-8") as f:
    f.write(code)
