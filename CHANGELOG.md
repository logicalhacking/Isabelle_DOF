# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

### Added

### Changed

- The project-specific configuration is not part of the `ROOT` file, the formerly 
  used `isadof.cfg` is obsolete and no longer supported.
- Removed explicit use of build script. Requires removing "build" script entry
  from ROOT files.
- Support for the `lipics` LaTeX style is now official. This requires document 
  option `document_comment_latex=true` in the ROOT file.
- Isabelle/DOF is now a proper Isabelle component that should be installed using the
  `isabelle components` command. The installation script is now only a convenience
  means for installing the required AFP entries.

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

[Unreleased]: https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF/compare/v1.2.0/Isabelle2021...HEAD
