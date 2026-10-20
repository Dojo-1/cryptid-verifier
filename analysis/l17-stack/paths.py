from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
FRONTIER=HERE.parent/'l17-stacked-section'
if not FRONTIER.is_dir():FRONTIER=HERE.parent/'l17-frontier'
HARDENING=HERE.parent/'l17-hardening'
