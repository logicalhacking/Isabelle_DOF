# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Changed

## 1.3.0 - 2022-07-08

### Changed

- The project-specific configuration is not part of the `ROOT` file, the formerly 
  used `isadof.cfg` is obsolete and no longer supported. 
- Removed explicit use of `document/build` script. Requires removing the `build` script 
  entry from ROOT files.
- Isabelle/DOF is now a proper Isabelle component that should be installed using the
  `isabelle components` command. The installation script is now only a convenient way 
  of installing the required AFP entries.
- `mkroot_DOF` has been renamed to `dof_mkroot` (and reimplemented in Scala).

## 1.2.0 - 2022-03-26

## 1.1.0 - 2021-03-20

### Added

- New antiquotations, consistency checks

### Changed

- Updated manual
- Restructured setup for ontologies (Isabelle theories and LaTeX styles)

## 1.0.0 - 2018-08-18

### Added

- First public release

[Unreleased]: https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/compare/v1.3.0/Isabelle2021...HEAD
[v1.3.0]: https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/compare/v1.2.0/Isabelle2021...v1.3.0/Isabelle2021-1
[v1.2.0]: https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/compare/v1.1.0/Isabelle2021...v1.2.0/Isabelle2021
[v1.1.0]: https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/compare/v1.0.0/Isabelle2019...v1.1.0/Isabelle2021
