# Changelog for PropaFP

## Unreleased changes

## [v0.1.1.0](https://github.com/rasheedja/PropaFP/compare/v0.1.0.0...v0.1.1.0)

- Remove quotes from FPTaylor variables, allowing support for FPTaylor >=0.9.3
- Re-enable `PropaFP.Expression.normalizeBoolean` in `PropaFP.DeriveBounds`
  - Aggressive simplification rules applied in `normalizeBoolean` are sometimes required to successfully derive bounds for variables
- Add `eliminate_if` transformation to the PropaFP Why3 driver
  - This transformation performs simplifications that PropaFP cannot currently do, making some problems easier for provers
- Regenerate Why3 SMT files using new driver
- Add test suite
  - Tests dReal(/LPPaver) and MetiTarski translators
  - Checks that PropaFP generated files are the same as the processed files stored under the examples folder

## [v0.1.0.0](https://github.com/rasheedja/PropaFP/tree/v0.1.0.0)

- Initial release
