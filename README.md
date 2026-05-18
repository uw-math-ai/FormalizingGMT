# FormalizingGMT

A Lean 4 project dedicated to formalizing core results from **Geometric Measure Theory (GMT)**, with an emphasis on measure‑theoretic foundations, rectifiability, and the structure of sets and measures in Euclidean spaces. This repository contributes to the growing ecosystem of mathematical formalization in Lean’s `mathlib`.

---

## Project Overview

This project aims to:

- Upstream foundational components to `mathlib`  
- Formalize classical results from Falconer's and Evan's GMT books.

The codebase is organized to keep mathlib‑ready components clean and modular.

Here is a poster we presented, it is not up to date, but gives a glimpse into our project structure.
![GMT Poster Presentation](.github/Assets/URS%20Formalizing%20GMTpng.png)


---

## Current Stage of the Project

> In Progress

Suggested structure:

- **Foundational components completed:**  
  - Proofs of 10 / 11 Lemmas

- **Actively in progress:**  
  - Cleaning of Lemma 3.3

- **Upcoming milestones:**  
  - Full Proof of the Theorem
  - More submissions to `mathlib`

---

## 🔗 Pull Requests to `mathlib`

| PR | Status | Description |
|----|--------|-------------|
| #32824 | Merged | Prove that the diameter of a Euclidean ball is twice its radius |
| #32851 | Merged | Introduces Theorem `exists_accPt_of_noAtoms` and lemma `discreteTopology_of_noAccPts ` |
| #00000 | Draft | Work in progress on `lemma_zero_of_pre_zero` : If at every sufficiently fine scale (all r ≤ δ), the set S appears to have zero size when measured at that resolution, then the set actually has zero size when measured with perfect resolution.|

---

## To-Do for Repo

- Fix versions of Lean and Mathlib in the Aristotle proofs
- Comment on the connection between `mathlib` PRs and proofs we will use

---

## Blueprint

The Lean blueprint lives in `blueprint/src` and is written in LaTeX so it can
compile to a dependency graph and linked web view.

Local build (from repo root):
- `leanblueprint web` (build the web version)
- `leanblueprint serve` (serve the built web version)
- `leanblueprint pdf` (build the PDF)
