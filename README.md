# Planetary Dispersion — Formal Mathematical Verification

[![Lean 4 Proof Verification](https://github.com/danielrportelli/PlanetaryDispersionMathCheck/actions/workflows/main.yml/badge.svg?branch=main)](https://github.com/danielrportelli/PlanetaryDispersionMathCheck/actions/workflows/main.yml)

This repository contains **Lean 4 and Mathlib proofs of selected mathematical properties** used in [Planetary Dispersion](https://danielportelli.com.au/planetarydispersion/), a real-time planetary auralisation and sound-design system developed in Unreal Engine.

The proofs address properties of the *formalised mathematical model*, including gas-mixture calculations, thermodynamic relationships and bounded audio-control mappings. They are intended to make the mathematical reasoning inspectable and reproducible, not to certify the entire application or the physical accuracy of its speculative planetary sound models.

## Proof files

| File | Focus |
| --- | --- |
| [`GasNormalisation.lean`](GasNormalisation.lean) | Normalisation of ten-gas mixtures, nonnegative fractions, mean molar mass and associated bounds. |
| [`PlanetaryDispersionThermodynamics.lean`](PlanetaryDispersionThermodynamics.lean) | Selected relationships and bounds involving heat capacity, gas properties, sound propagation and unit conversions. |
| [`PlanetaryDispersionAudioMappings.lean`](PlanetaryDispersionAudioMappings.lean) | Selected positivity and boundedness properties of environmental and nine-band audio-control mappings. |
| [`PlanetaryDispersionPowerLawChecks.lean`](PlanetaryDispersionPowerLawChecks.lean) | Pressure and temperature power-law corrections, their clamps, the near-vacuum branch and overall multiplier bounds. |

### Examples of machine-checked properties

- **Mean molar mass:** For a valid, nonnegative, normalised mixture of the ten supported gases, the formalised model bounds mean molar mass between **0.002016 and 0.064063 kg/mol**.
- **Mixture heat capacity:** The formal model establishes bounds from its fixed per-gas heat-capacity constants, assuming nonnegative fractions summing to one.
- **Environmental multiplier:** The formalised pressure/temperature correction, including its near-vacuum branch, satisfies **0.48 ≤ M_env ≤ 3.9**.

These are **conditional mathematical results**: the assumptions and definitions in each `.lean` file determine precisely what has been proved.

## Reproduce the verification

The repository includes `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` to specify its Lean/Mathlib environment. With [Lean 4 / elan](https://lean-lang.org/) and Git installed, clone the repository and run:

```bash
git clone https://github.com/danielrportelli/PlanetaryDispersionMathCheck.git
cd PlanetaryDispersionMathCheck
lake exe cache get

lake env lean GasNormalisation.lean
lake env lean PlanetaryDispersionThermodynamics.lean
lake env lean PlanetaryDispersionAudioMappings.lean
lake env lean PlanetaryDispersionPowerLawChecks.lean
```

For reproducibility, use the committed `lake-manifest.json`. Avoid running `lake update` unless you deliberately intend to change the dependency versions; it can alter the environment in which the proofs are checked.

A command that exits with status `0` has successfully checked the corresponding file. Informational output and nonfatal linter warnings may still appear.

### Automated checks

The [GitHub Actions workflow](https://github.com/danielrportelli/PlanetaryDispersionMathCheck/actions/workflows/main.yml) checks all four `.lean` files on pushes to `main` and on pull requests targeting `main`. The badge at the top of this README reflects the status of that workflow on `main`.

**A passing workflow means the specified Lean files were accepted by Lean in that run.** On its own, it does not demonstrate that every theorem is free of admitted proofs, or that the Lean definitions exactly match every Unreal Engine Blueprint.

For further inspection, Lean's `#print axioms` command reports the axiom dependencies of individual theorems. Selected checks in this project have returned the standard dependencies `propext`, `Classical.choice` and `Quot.sound`, without `sorryAx`; this should not be taken as an exhaustive axiom audit of every theorem.

## Scope and limitations

Formal verification establishes that stated propositions follow from the definitions and hypotheses encoded in Lean. It does **not**, by itself, establish:

- numerical identity between Lean's real-number model and Unreal Engine's floating-point Blueprint/MetaSound implementation;
- validity of the model's chosen per-gas nine-band coefficients, exponents, clamps or creative calibration weights as measured physical constants;
- experimental accuracy of atmospheric absorption, temporal dispersion or audible results for all planetary environments; or
- correctness of the entire audio-processing signal chain or application runtime.

The [Planetary Dispersion Technical Guide](https://danielportelli.com.au/planetarydispersion/) describes the mathematical model, Blueprint architecture, MetaSound processing and modelling limitations. It should be consulted alongside these proofs.

## Project and attribution

**Planetary Dispersion** — Daniel Portelli, 2026  
Project website: https://danielportelli.com.au/planetarydispersion/

This repository documents selected formal verification work associated with the project. For project materials and licensing information, consult the main project website. No separate licence for this repository is asserted by this README.
