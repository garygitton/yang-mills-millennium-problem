import Lake
open Lake DSL

package «yang-mills-millennium-problem» where
  version := v!"1.0.0"
  description := "Constructive Proof and Formal Lean 4 Verification of 4D Yang-Mills Existence and Mass Gap"
  keywords := #["mathematics", "physics", "yang-mills", "mass-gap", "formal-verification", "lean4", "constructive-qft"]
  author := "Gary Gitton"
  license := "CC-BY-NC-SA-4.0"

@[default_target]
lean_lib «YangMills» where
  srcDir := "proofs"
