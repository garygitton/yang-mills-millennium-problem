/-
Copyright (c) 2026 Gary Gitton. All rights reserved.
Author: Gary Gitton
Title: Constructive 4D Yang-Mills Existence and Strictly Positive Mass Gap (Architectural Blueprint)
Description: Master root library entrypoint for machine-checked formal verification.
Problem: Clay Mathematics Institute Millennium Prize Problem (Jaffe & Witten, 2000)
Status: Formal Architectural Blueprint & Conditional Reduction Specification for 4D Yang-Mills Theory in Lean 4
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Hilbert
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Basic

-- Module 1: Foundational Gauge Groups & Osterwalder-Schrader Axioms (OS0-OS4)
import YangMills.Axioms

-- Module 2: Gauge Orbit Space Orbifold Regularity & Palais Slice Charts
import YangMills.OrbitGeometry

-- Module 3: Loop Space Horizontal Curvature & Bochner-Weitzenböck Spectral Gap
import YangMills.BochnerRicci

-- Module 4: Balaban Multiscale Polymer Renormalization Group
import YangMills.Renormalization

-- Module 5: GNS Construction, Reflection Positivity & Friedrichs Extension
import YangMills.FunctionalAnalysis

-- Module 6: Non-Trivial Topological Sectors & ADHM Instantons
import YangMills.Topology

-- Module 7: Holographic Soft-Wall Bulk & Sturm-Liouville Resolvent Compactness
import YangMills.Holography

-- Module 8: Schwartz Test Space, Tempered Distributions & Haag-Ruelle Scattering
import YangMills.Scattering

-- Module 9: Non-Perturbative Dimensional Transmutation & Clay Millennium Mass Gap
import YangMills.MassGap

-- Module 10: Explicit Constructive Evaluation & Non-Vacuity Certificates
import YangMills.Evaluation

-- Module 11: Balaban Multiscale Small-Field Sobolev Bounds
import YangMills.BalabanSobolev

-- Module 12: Balaban-Kotecky-Preiss Polymer Cluster Expansion
import YangMills.BalabanCluster

-- Module 13: Balaban-Wilson Algebra Radon Measure Representation
import YangMills.BalabanRadon

-- Module 14: Balaban Continuum Reduction & Millennium Specification
import YangMills.BalabanContinuum

-- Module 15: Infinite-Dimensional Bakry-Émery Geometry & Spectral Gap
import YangMills.BakryEmery

-- Module 16: Clay Mathematics Institute Millennium Specification & Universal Bridge
import YangMills.ClaySpecification
import YangMills.MathlibIntegration

-- Module 17: Kerr-Schild Double Copy & Ryu-Takayanagi Entanglement Confinement
import YangMills.KerrSchildDoubleCopyRyuTakayanagi

-- Module 18: Sobolev Compact Embedding & Rellich-Kondrachov Resolvent
import YangMills.SobolevCompactEmbedding

-- Module 19: Sturm-Liouville Resolvent Compactness & Dilaton Spectral Gap
import YangMills.SturmLiouvilleResolvent

-- Module 20: Yang-Mills Spectral Mass Gap Master Theorem
import YangMills.YangMillsMassGap

/-- Canonical profile type aliases for Mathlib Yang-Mills alignment -/
def WightmanQFT := @YangMills.Axioms.WightmanQFT
def GaugeField := @YangMills.Axioms.GaugeField
def YangMillsAction := @YangMills.Axioms.YangMillsAction
