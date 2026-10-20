import Lake
open Lake DSL

/-! Links our macro systems to the machine-level Lean proofs of Dos Santos et al.
    (github.com/google-deepmind/cryptids, pinned commit), which show for each machine
    `IsHalt target ↔ CollatzHalts next start` from the blank tape. -/
package «cryptid-link» where

require «antihydra-ouroboros» from ".."
require Cryptids from git "https://github.com/google-deepmind/cryptids" @ "a0c1f56af53a76e985a656032b48015f7e48921b"

@[default_target]
lean_lib «CryptidLink» where
