import os, re, shutil
from pathlib import Path

# 定义语言目录映射
lang_dirs = {
    "rust": "examples/algorithms-rust/src/leetcode",
    "python": "examples/algorithms-python/src/leetcode",
    "go": "examples/algorithms-go/leetcode",
    "typescript": "examples/algorithms-ts/src",
    "java": "examples/algorithms-java/src/main/java/leetcode",
    "cpp": "examples/algorithms-cpp/leetcode",
    "c": "examples/algorithms-c",
    "js": "examples/algorithms-js/leetcode",
}

# 提取题号的正则
lc_pattern = re.compile(r'lc(\d{4})_(.+?)\.(\w+)$')

# 收集所有LeetCode文件
problems = {}  # {题号: {名称, {语言: [文件路径]}}}

for lang, base_dir in lang_dirs.items():
    p = Path(base_dir)
    if not p.exists():
        continue
    for f in p.rglob('*'):
        if not f.is_file():
            continue
        m = lc_pattern.match(f.name)
        if m:
            num, name, ext = m.groups()
            key = f"lc{num}"
            if key not in problems:
                problems[key] = {"name": name, "files": {}}
            if lang not in problems[key]["files"]:
                problems[key]["files"][lang] = []
            problems[key]["files"][lang].append(str(f))
        else:
            # 非LeetCode文件，稍后处理
            pass

# 创建by-algorithm目录并移动文件
base = Path("examples/by-algorithm")
base.mkdir(parents=True, exist_ok=True)

for key, data in sorted(problems.items()):
    prob_dir = base / key
    prob_dir.mkdir(exist_ok=True)
    
    # 为每种语言创建子目录并移动文件
    for lang, files in data["files"].items():
        lang_dir = prob_dir / lang
        lang_dir.mkdir(exist_ok=True)
        for src in files:
            src_path = Path(src)
            dest = lang_dir / src_path.name
            shutil.move(str(src_path), str(dest))

print(f"Created {len(problems)} algorithm directories in examples/by-algorithm/")
print("Sample:")
for key in list(sorted(problems.keys()))[:5]:
    langs = ", ".join(problems[key]["files"].keys())
    print(f"  {key}: {langs}")
