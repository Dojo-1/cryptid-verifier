import Lake
open Lake DSL

package «cryptid-real» where

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"
require «antihydra-ouroboros» from ".."

@[default_target]
lean_lib «CryptidReal» where
