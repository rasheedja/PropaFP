# Changelog for PropaFP

## Unreleased changes

- Remove quotes from FPTaylor variables, allowing support for FPTaylor >=0.9.3
- Re-enable `PropaFP.Expression.normalizeBoolean` in `PropaFP.DeriveBounds`
  - Aggressive simplification rules applied in `normalizeBoolean` are sometimes required to successfully derive bounds for variables

## [v0.1.0.0](https://github.com/rasheedja/propaFP/tree/0.1.0.0)

- Initial release
