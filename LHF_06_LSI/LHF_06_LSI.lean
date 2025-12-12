-- Import the HPDE-03 wiring (provides concrete Gaussian LSI infrastructure)
import LHF_06_LSI.LHF_06_HPDE_wiring

/-!
# LHF-06: Log-Sobolev Inequality Framework

This is the root module for the LHF-06 Log-Sobolev package.
It provides the connection from Bakry-Émery curvature to concentration inequalities.

## Main Components

1. `LHF_06_HPDE_wiring`: Connection to HPDE-03's Gaussian LSI infrastructure
2. `LHF_06_manual`: Abstract BEH → LSI framework and proof sketch

## Usage

Import this module to get:
- Access to HPDE-03's proven Gaussian concentration theorems
- The Gaussian LSI and Poincaré axioms
- NS-specific application theorems for Spectral Lock analysis
-/
