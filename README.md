# [Isabelle/DOF](https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF): Document Preparation Setup

Isabelle/DOF is a novel Document Ontology Framework on top of Isabelle.
Isabelle/DOF allows for both conventional typesetting and formal development.
The manual for [Isabelle/DOF 1.3.0/Isabelle2021-1 is available
online.](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.pdf)

## Pre-requisites

Isabelle/DOF has three major prerequisites:

* **Isabelle:** Isabelle/DOF requires [Isabelle
  2022](https://isabelle.in.tum.de/website-Isabelle2022/). Please download the
  Isabelle 2022 distribution for your operating system from the [Isabelle
  website](https://isabelle.in.tum.de/website-Isabelle2022/).
* **AFP:** Isabelle/DOF requires several entries from the [Archive of Formal Proofs
  (AFP)](https://www.isa-afp.org/).  Please install the AFP following the
  instructions given at <https://www.isa-afp.org/using.html>.
* **LaTeX:** Isabelle/DOF requires a modern LaTeX installation, i.e., at least
  [TeX Live 2022](https://www.tug.org/texlive/) with all available updates
  applied.
  
## Installation

Isabelle/DOF is provided as an Isabelle component. After installing the
prerequisites, change into the directory containing Isabelle/DOF (this should be
the directory containing this `README.md` file) and execute the following 
command for building the standard sessions of Isabelle/DOF:

```console
foo@bar:~$ isabelle build -D . -x Isabelle_DOF-Proofs -x HOL-Proofs
```

This will compile Isabelle/DOF and run the example suite.

## Usage

### Opening an Example

If you want to work with or extend one of the examples, e.g., you can open it
similar to any standard Isabelle theory:

```console
isabelle jedit -d . -l Isabelle_DOF Isabelle_DOF-Example-Scholarly_Paper/IsaDofApplications.thy
```

This will open an example of a scientific paper using the pre-compiled session
``Isabelle_DOF``, i.e., you will not be able to edit the default ontologies
defined in the ``Isabelle_DOF`` session.  If you want to edit the ontology definition, 
just open the theory file with the session ``Functional-Automata``:

```console
isabelle jedit -d . -l Functional-Automata Isabelle_DOF-Example-Scholarly_Paper/IsaDofApplications.thy
```

While this gives you more flexibility, it might "clutter" your editing
experience, as a lot of internal theories are loaded into Isabelle's editor.

## Releases

For releases, signed archives including a PDF version of the Isabelle/DOF manual
are available. The latest release is **Isabelle/DOF 1.3.0/Isabelle2021-1**:

* [Isabelle_DOF-1.3.0_Isabelle2021-1.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.pdf)
* [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz)
* [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc)

Older releases are available [here.](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/)

## Repository Structure

The ``main`` branch of this Repository is developed using the latest official
release of Isabelle (which is, at point of writing, Isabelle 2022). This is also
the main development branch. In addition, he ``Isabelle_dev`` branch is used for
testing Isabelle/DOF with the latest development version of Isabelle.

This repository is structured into several Isabelle sessions, each of which is stored
in a subdirectory:

* [Isabelle_DOF](./Isabelle_DOF/): This is the main session, providing the
  Isabelle/DOF system. Furthermore, this session is currently under
  consideration for a submission to the AFP.
* [Isabelle_DOF-Example-Scholarly_Paper](./Isabelle_DOF-Example-Scholarly_Paper/):
  This session provides an example document written Isabelle/DOF. It only
  requires the core ontologies provided by the ``Isabelle_DOF`` session.
  Furthermore, this session is currently under consideration for a submission to
  the AFP.
* [Isabelle_DOF-Ontologies](./Isabelle_DOF-Ontologies/): This session provided
  additional ontologies and document templates.
* [Isabelle_DOF-Unit-Tests](./Isabelle_DOF-Unit-Tests/): This session includes
  various tests for the Isabelle/DOF system, partly depending on the ontologies
  provided by the ``Isabelle_DOF-Ontologies`` session.
* [Isabelle_DOF-Example-Extra](./Isabelle_DOF-Examples-Extra/): This directory
  contains additional example documents written using the Isabelle/DOF systems,
  each of which is defined in an own subdirectory.
* [Isabelle_DOF-Proofs](./Isabelle_DOF-Proofs/): This session provides the
  Isabelle/DOF systems with proof objects. This is required for the deep
  ontology embedding.

## Team

Main contacts:

* [Achim D. Brucker](http://www.brucker.ch/)
* [Burkhart Wolff](https://www.lri.fr/~wolff/)

### Contributors

* Idir Ait-Sadoune
* Paolo Crisafulli
* Chantal Keller
* Nicolas Méric

## License

This project is licensed under a 2-clause BSD license.

SPDX-License-Identifier: BSD-2-Clause

## Publications

* Achim D. Brucker, Idir Ait-Sadoune, Paolo Crisafulli, and Burkhart Wolff.
  [Using The Isabelle Ontology Framework: Linking the Formal with the
  Informal](https://www.brucker.ch/bibliography/download/2018/brucker.ea-isabelle-ontologies-2018.pdf).
  In Conference on Intelligent Computer Mathematics (CICM). Lecture Notes in
  Computer Science (11006), Springer-Verlag, 2018.
  [doi:10.1007/978-3-319-96812-4_3](https://doi.org/10.1007/978-3-319-96812-4_3).

* Achim D. Brucker and Burkhart Wolff. [Isabelle/DOF: Design and
  Implementation](https://www.brucker.ch/bibliography/download/2019/brucker.ea-isabelledof-2019.pdf).
  In Software Engineering and Formal Methods (SEFM). Lecture Notes in Computer
  Science (11724), Springer-Verlag, 2019.
  [doi:10.1007/978-3-030-30446-1_15](https://doi.org/10.1007/978-3-030-30446-1_15).

* Achim D. Brucker, Burkhart Wolff. [Using Ontologies in Formal Developments
  Targeting
  Certification](https://www.brucker.ch/bibliography/download/2019/brucker.ea-ontologies-certification-2019.pdf).
  In Integrated Formal Methods (IFM). Lecture Notes in Computer Science (11918).
  Springer-Verlag 2019.
  [doi:10.1007/978-3-030-34968-4_4](http://dx.doi.org/10.1007/978-3-030-34968-4_4)  

* Sergio Bezzecchi, Paolo Crisafulli, Charlotte Pichot, and Burkhart Wolff.
  [Making Agile Development Processes fit for V-style Certification
   Procedures.](https://hal.archives-ouvertes.fr/hal-01702815/document). In ERTS
   2018. <https://hal.archives-ouvertes.fr/hal-01702815>

## Upstream Repository

The upstream git repository, i.e., the single source of truth, for this project
is hosted at <https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF>.
