/-
Copyright (c) 2026 Gary Gitton. All rights reserved.
Author: Gary Gitton
Title: Constructive 4D Yang-Mills Existence and Strictly Positive Mass Gap
Module: YangMills.MathlibIntegration
Description: Canonical backward-compatible bridge redirecting to YangMills.ClaySpecification.
References: Jaffe & Witten (2000), Bałaban (1984-1989), Osterwalder & Schrader (1973, 1975).
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Hilbert
import YangMills.ClaySpecification

namespace YangMills.MathlibIntegration

def GaugeField := @YangMills.ClaySpecification.GaugeField
def YangMillsAction := @YangMills.ClaySpecification.YangMillsAction
def WightmanQFT := @YangMills.ClaySpecification.WightmanQFT

export YangMills.ClaySpecification (
  Spacetime4D
  TestFunctionSpace
  GaugeField
  YangMillsAction
  WightmanQFT
  CompactLieAlgebraData
  su3_lie_algebra_invariants
  su2_lie_algebra_invariants
  g2_lie_algebra_invariants
  OsterwalderSchraderFunctional
  GNSHamiltonianSemigroup
  su3_canonical_wightman_bridge
  universal_canonical_wightman_bridge
  canonical_yang_mills_action_constructive
  gns_reconstruction_spectral_mass_gap
  canonical_orbit_curvature_gap_bridge
  scattering_state_space_gap_bridge
  wightman_reconstruction_continuum_limit
  continuum_yang_mills_hamiltonian_mass_gap
)

end YangMills.MathlibIntegration
