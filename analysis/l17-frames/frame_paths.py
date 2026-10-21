from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
HARDENING=HERE.parent/'l17-hardening'
FRONTIER=HERE.parent/'l17-stacked-section'
sys.dont_write_bytecode=True
sys.path[:0]=[str(HARDENING),str(FRONTIER)]
