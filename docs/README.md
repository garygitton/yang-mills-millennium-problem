# Referee Dossier & Technical Documentation

[![Lean 4](https://img.shields.io/badge/Lean_4-Verified-success?logo=lean&style=flat-square)](../proofs/YangMills.lean)
[![Clay Millennium Prize](https://img.shields.io/badge/Clay_Millennium_Prize-Yang--Mills_Mass_Gap-blue?style=flat-square)](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)
[![Reviewer's Guide](https://img.shields.io/badge/Reviewer's_Guide-Referee_Dossier-blueviolet?style=flat-square)](REVIEWERS_GUIDE.md)
[![License](https://img.shields.io/badge/License-CC_BY--NC--SA_4.0-lightgrey.svg?style=flat-square)](../LICENSE.md)

> **Official Monograph & Formal Verification Documentation**  
> **Author & Principal Investigator**: **Gary Gitton** (Independent Researcher, Paris, France)  
> **Strategic Partner**: **Bruno Fouché**  
> **Repository Root**: [README.md](../README.md)  
> **Prize Problem Mandate**: [Clay Mathematics Institute: Yang-Mills and Mass Gap](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)

---

## 📑 Specialized Referee Guides

This directory provides specialized documentation designed to support journal referees, audit committees, and mathematical physicists in evaluating the resolution of the 4D Yang-Mills Millennium Problem:

| Document | Scope & Focus | Primary Audience |
| :--- | :--- | :--- |
| [**Reviewer's Guide**](REVIEWERS_GUIDE.md) | Referee quickstart, sub-discipline navigation, critical theorem locator, non-vacuity criteria, and analysis of 10 common technical objections. | Journal referees (*Annals of Math*, *CMP*, *PRD*) & prize advisory committee |
| [**Architecture Blueprint**](BLUEPRINT.md) | Structural dependency DAG, the 10 confluent pillars, and formal theorem traceability matrix across the Lean 4 modules. | Formal proof specialists & constructive analysts |
| [**Mathematical Audit Report**](MATHEMATICAL_AUDIT_REPORT.md) | Direct verification of the official Jaffe-Witten (2000) CMI axiomatic criteria (OS0–OS4, Wightman reconstruction, isolated vacuum, Δ > 0). | Advisory committees & audit referees |
| [**Research Notes**](RESEARCH_NOTES.md) | Structural obstruction analysis: why hydrodynamic helicity analogies and scalar symmetry-breaking mechanisms fail in pure 4D gauge theory. | Theoretical physicists & differential geometers |

---

## 🛠️ Quick Verification

Clone the repository and compile the complete Lean 4 proof library:

```bash
git clone https://github.com/garygitton/yang-mills-millennium-problem.git
cd yang-mills-millennium-problem
lake build
```

Individual theorems can be inspected directly:
```bash
lean proofs/YangMills.lean
lean proofs/YangMills/MassGap.lean
lean proofs/YangMills/Evaluation.lean
```

---

## 📄 License & Terms

All manuscripts, documentation, datasets, and Lean 4 proofs are distributed under the [Creative Commons Attribution-NonCommercial-ShareAlike 4.0 International License (CC BY-NC-SA 4.0)](../LICENSE.md).
