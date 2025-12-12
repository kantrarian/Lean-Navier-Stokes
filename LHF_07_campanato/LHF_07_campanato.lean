-- Import the HPDE-04 wiring (provides concrete infrastructure)
import LHF_07_campanato.LHF_07_HPDE_wiring

/-!
# LHF-07: Campanato Embedding Theorem

This is the root module for the LHF-07 Campanato embedding package.
It provides the "regularity bridge" from energy estimates to Hölder continuity.

## Main Components

1. `LHF_07_HPDE_wiring`: Connection to HPDE-04's Campanato infrastructure
2. `LHF_07_manual`: Abstract framework and proof sketch

## Usage

Import this module to get:
- Access to HPDE-04's proven Campanato lemmas
- The Campanato-Hölder embedding axiom
- NS-specific application theorems
-/
