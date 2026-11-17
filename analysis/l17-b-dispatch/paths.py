from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.dont_write_bytecode = True
sys.path[:0] = [str(BASE / 'l17-hardening'), str(BASE / 'l17-stacked-section')]
