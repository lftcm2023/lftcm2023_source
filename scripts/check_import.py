"""
Print the list of lean files in the LftCM folder that do not import LftCM.Common
"""
from pathlib import Path

for path in (Path(__file__).parent.parent/"LftCM").glob("**/*.lean"):
    if not any([l == "import LftCM.Common" for l in path.read_text().split("\n")]):
        print(path)
