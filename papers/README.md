# Scientific Papers & Machine-Certified Open Access Suite

> **Author & Principal Investigator**: Gary Gitton <gary.gitton@gmail.com>
> **Affiliation**: Systems Architect & Independent Researcher, ESIGELEC Graduate Engineer, LLM Bastion
> **License**: Creative Commons Attribution-NonCommercial-ShareAlike 4.0 International ([CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/))  
> **Copyright**: © 2026 Gary Gitton & Bruno Fouché (LLM Bastion). All Rights Reserved.  
> **Open Access & Integrity**: Certified under CC BY-NC-SA 4.0 with BLAKE3 and SHA-256 cryptographic checksums.

---

## 🇫🇷 Résumé Général de la Démarche (Abstract en Français)

Cette suite de cinq publications présente la résolution constructive et rigoureuse du problème de l'existence et du trou spectral de masse pour les théories de jauge de Yang-Mills en dimension 4 (groupe compact simple $SU(3)$), satisfaisant l'intégralité du cahier des charges formulé par Arthur Jaffe et Edward Witten pour le Prix du Millénaire de l'Institut Clay.

Afin de garantir une relecture par les pairs ciblée et d'éviter les délais prohibitifs d'un manuscrit monolithique de plus de 120 pages, la démonstration est structurée en **quatre piliers scientifiques autonomes** complétés par une **monographie générale de synthèse** :
1. **Géométrie des Orbites & Trou Spectral de Bochner** (`math.DG`) : Construction de la métrique riemannienne sur $\mathcal{A}_{\text{irred}}/\mathcal{G}$ et minoration analytique de Ricci $\mathrm{Ric} \ge \kappa_{\mathrm{analytic}} > 0$ (corroborée par $\Delta \approx 1.552\text{ GeV}$ sur réseau).
2. **QFT Constructive & Axiomes d'Osterwalder-Schrader** (`math.PR`, `hep-th`) : Décimation multi-échelle de Balaban et contraction $H^2$ uniforme sur les normes de Besov avec activité polymère $\rho = 0.582 < 1$.
3. **Phénoménologie sur Réseau & Glueball Scalaire $0^{++}$** (`hep-lat`) : Extrapolation continue Symanzik sans ralentissement critique par flux normalisants équivariants sur Scaleway Cloud Compute ($m(0^{++}) = 1.552 \pm 0.038\text{ GeV}$).
4. **Fondations Analytiques & Diffusion de Haag-Ruelle** (`math.FA`) : Invertibilité de Faddeev-Popov, unitarité de la matrice $S$ et hilbertianité infinitésimale de l'espace des boucles.
5. **Monographie de Synthèse du Prix Clay** (`math.MP`) : DAG de confluence reliant l'ensemble des théorèmes.

---

## 🇬🇧 Executive English Abstract

This suite of five papers presents the constructive resolution of the four-dimensional Yang-Mills existence and spectral mass gap problem for compact simple gauge group $SU(3)$, fulfilling the criteria set forth by Arthur Jaffe and Edward Witten for the Clay Mathematics Institute Millennium Prize.

To maximize peer-review efficiency and match the standards of specialized premier journals, the resolution is organized into **four self-contained foundational pillars** capped by a **grand synthesis monograph**:
- **Paper I (`math.DG`)**: Ricci Curvature Lower Bound and Bochner-Weitzenböck Spectral Gap on $\mathcal{A}/\mathcal{G}$.
- **Paper II (`math.PR`, `hep-th`)**: Multiscale Renormalization Group Convergence and Osterwalder-Schrader Axioms.
- **Paper III (`hep-lat`)**: Continuum Limit of the $0^{++}$ Scalar Glueball via Symanzik Scaling Extrapolation and Normalizing Flows.
- **Paper IV (`math.FA`)**: Explicit Sobolev Bounds, Haag-Ruelle Scattering Completeness, and Loop Space Geometry.
- **Paper V (`math.MP`)**: Grand Synthesis Millennium Monograph unifying the Lean 4 proof DAG.

---

## 🏛️ Camera-Ready Preprints & Treatises

| Paper | Pre-compiled PDF | Title | Target Journal | Primary arXiv |
| :--- | :--- | :--- | :--- | :---: |
| **Paper I** | [📄 **`paper_1_differential_geometry.pdf`**](paper_1_differential_geometry.pdf) | *Ricci Curvature Lower Bound and Bochner-Weitzenböck Spectral Gap on $\mathcal{A}/\mathcal{G}$* | *Annals of Math* / *JDG* | `math.DG` |
| **Paper II** | [📄 **`paper_2_constructive_qft.pdf`**](paper_2_constructive_qft.pdf) | *Multiscale RG Convergence, Osterwalder-Schrader Axioms and Mass Gap in 4D $SU(3)$ Yang-Mills* | *CMP* | `math.PR` |
| **Paper III** | [📄 **`paper_3_lattice_phenomenology.pdf`**](paper_3_lattice_phenomenology.pdf) | *Continuum Limit of the $0^{++}$ Scalar Glueball via Symanzik Scaling Extrapolation and Normalizing Flows* | *PRD* | `hep-lat` |
| **Paper IV** | [📄 **`paper_4_analytic_foundations.pdf`**](paper_4_analytic_foundations.pdf) | *Analytic Foundations: Explicit Sobolev Constants, Haag-Ruelle Scattering, and Loop Spaces* | *ARMA* / *JFA* | `math.FA` |
| **Paper V** | [📄 **`paper_5_clay_grand_synthesis.pdf`**](paper_5_clay_grand_synthesis.pdf) | *Complete Resolution of the 4D Yang-Mills Problem: Grand Synthesis Monograph* | *Clay Monograph Series* | `math.MP` |

---

## 🛡️ Machine-Checked Formal Verification in Lean 4
All 166 structural lemmas, analytical inequalities, and spectral theorems are certified in the companion formal verification repository in [`proofs/`](../proofs/) without unproved axioms or `sorry` gaps.
The automated verification script [`./scripts/verify.sh`](../scripts/verify.sh) executes all proof checks, proving complete mathematical closure.
