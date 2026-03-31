# exact-fixed-addend-modadd-theory

Public release of the manuscript:

**Exact Fixed-Addend Differential and Linear Theory of Modular Addition with Linear-Time Algorithms**

## Status

This repository is the primary public record of the current work.

A previous archive submission was not accepted under editorial criteria.  
I am therefore publishing the work here in the open, together with public validation materials, instead of continuing to negotiate with a gateway that did not accept it.

This repository is **not** a peer-reviewed publication venue.  
Readers should judge the work from the mathematics, algorithms, verification logic, and reproducible engineering material provided here.

## Why this repository exists

I will say this plainly.

This work was not written casually.  
It was built through substantial theorem-level derivation, implementation work, reconstruction effort, and verification effort.

I do **not** accept the idea that this work lacked creativity, lacked effort, or lacked technical seriousness.  
If an editorial gate does not want to carry it, then fine — the work will stand in public on its own.

So this repository is not an apology, and not a plea for approval.  
It is a technical release made in full view.

Call it anger if you want.  
But it is not random emotion.  
It is engineered anger: the kind that turns rejection into a public technical record.

## What this work claims

This repository accompanies a manuscript that develops exact fixed-addend analysis for the unary map

`x -> x + ConstantKey (mod 2^n)`

and claims the following core results:

- An exact 4-state carry-pair formulation for XOR differentials of fixed-addend modular addition
- An exact 2-state carry-transfer formulation for fixed-addend linear correlations
- Explicit linear-time evaluators for both quantities
- Exhaustive small-width implementation checks against brute force

## Repository contents

- `paper/`  
  Public manuscript PDF and release material

- `matrix_repro_check.cpp`  
  Standalone appendix-kernel audit for the local differential and linear matrices

- `miyano_fixed_addend_verifier_readable.cpp`  
  Readable single-file verifier / reproducer for the fixed-addend differential and linear core

- `notes/`  
  Status notes, release notes, and repository policy text

## What is public here

The goal of this repository is to make the **technical content** public:

- the manuscript PDF
- the public verification / reproduction code
- the public release notes
- the repository history of the public version

## What is NOT public here

The LaTeX manuscript source is **not** public.

I am intentionally keeping the editable manuscript source under my own control.  
I do not want uncontrolled third-party rewrites, forked manuscript branches, or silent derivative versions of the paper text.

To say it more directly:

- I am willing to publish the paper
- I am willing to publish technical code
- I am willing to publish verification material
- I am **not** willing to give away editorial control of the manuscript source itself

If you want to seriously improve, extend, or co-develop the manuscript at the source level, contact me first.

## Collaboration policy

If you have serious technical interest in this work, you are welcome to reach out.

However, editable manuscript source is not distributed by default.  
It may be shared only in an explicit collaboration context, such as:

- a genuine technical collaboration
- a co-authorship discussion
- a jointly agreed revision effort
- a clearly scoped verification / extension project

No such collaboration is implied merely by reading this repository.

## License and usage policy

### Code

Unless otherwise stated, code files in this repository are intended to be released under:

**GNU General Public License v3.0 or later**

This means code reuse and modification must remain under GPL-compatible terms.

### Manuscript and paper text

The manuscript PDF, paper text, release wording, and non-code writing in this repository are **not** released as editable manuscript source.

Public reading, citation, and discussion are welcome.  
But manuscript-level derivative editing, rewriting, or redistribution of editable source is not granted here by default.

If manuscript-source-level work is desired, contact me first.

## What readers should do

Do not treat this repository as a prestige signal.  
Treat it as a technical object.

If you want to evaluate it seriously, check:

- whether the differential recurrence is internally coherent
- whether the linear transfer formulation is internally coherent
- whether the claimed linear-time evaluators match the stated recurrences
- whether the public verifier logic actually matches the paper objects
- whether the exhaustive checks are sufficient for the scope claimed

That is the level on which this work should be attacked or defended.

## Build notes

Example compilation commands for the standalone C++ files:

```bash
g++ -O3 -std=c++20 -march=native matrix_repro_check.cpp -o matrix_repro_check
g++ -O3 -std=c++20 -march=native miyano_fixed_addend_verifier_readable.cpp -o miyano_fixed_addend_verifier_readable
```

## Citation

If you reference this work, please cite the manuscript title and the corresponding GitHub release or commit.

## Contact

For technical discussion, verification questions, or serious collaboration proposals, use the repository issue tracker or the contact method listed on the GitHub profile.

## Final note

This repository exists because I chose publication over silence.

If an editorial gate refuses to carry the work, that does not erase the work.
It only changes where the work must stand.

So it stands here.
