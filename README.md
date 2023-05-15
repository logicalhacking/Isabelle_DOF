# [Isabelle/DOF](https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF): Document Preparation Setup

Isabelle/DOF is a novel Document Ontology Framework on top of Isabelle.
Isabelle/DOF allows for both conventional typesetting and formal development.

## Pre-requisites

Isabelle/DOF has two major prerequisites:

* **Isabelle:** Isabelle/DOF requires [Isabelle](https://isabelle.in.tum.de/)
  and several entries from the [Archive of Formal Proofs
  (AFP)](https://www.isa-afp.org/).
* **LaTeX:** Isabelle/DOF requires a modern LaTeX installation, i.e., at least
  [TeX Live 2022](https://www.tug.org/texlive/) with all available updates
  applied.
  
## Installation

<!--
Isabelle/DOF is available as part of the [Archive of Formal Proofs
(AFP)](https://www.isa-afp.org/). This is the most convenient way to install
Isabelle/DOF for the latest official release of Isabelle.

### Installation from the Archive of Formal Proofs (AFP)

Isabelle/DOF is available in the AFP. Hence, for using Isabelle/DOF with the
latest official released version of Isabelle, please download the Isabelle
distribution for your operating system from the [Isabelle
website](https://isabelle.in.tum.de/). Furthermore, please install the AFP
following the instructions given at <https://www.isa-afp.org/help.html>.

Isabelle/DOF is currently consisting out of three AFP entries:

* [Isabelle_DOF:](https://www.isa-afp.org/entries/Isabelle_DOF.html) This entry
  contains the Isabelle/DOF system itself, including the Isabelle/DOF manual.
* [Isabelle_DOF-Example-I:](https://www.isa-afp.org/entries/Isabelle_DOF-Example-I.html)
  This entry contains an example of an academic paper written using the
  Isabelle/DOF system.
* [Isabelle_DOF-Example-II:](https://www.isa-afp.org/entries/Isabelle_DOF-Example-II.html)
  This entry contains an example of an academic paper written using the
  Isabelle/DOF system.

-->

### Installation of the Development Version (Git Repository)

The development version of Isabelle/DOF that is available in this Git repository
provides, over the AFP version, additional ontologies, document templates, and
examples that might not yet "ready for general use". Furthermore, as it is
provided as an Isabelle component, it can also provide additional tools that
cannot be distributed via the AFP. For more details on installing the
development version, please consult the
[README_DEVELOPMENT.md](./README_DEVELOPMENT.md) file.

After installing the prerequisites, change into the directory containing
Isabelle/DOF (this should be the directory containing this ``README.md`` file)
and execute the following command for building the standard sessions of
Isabelle/DOF:

```console
foo@bar:~$ isabelle build -D . -x Isabelle_DOF-Proofs -x HOL-Proofs
```

This will compile Isabelle/DOF and run the example suite.

For building the session ``Isabelle_DOF-Proofs``, the timeout might need to 
increased to avoid timeouts during building the dependencies:

```console
foo@bar:~$ isabelle build -d . -o 'timeout_scale=2' Isabelle_DOF-Proofs
```

## Usage

In the following, we assume that you installed Isabelle/DOF either from the AFP
(adding the AFP as a component to your Isabelle system) or from the Git
repository of Isabelle/DOF (installing Isabelle/DOF as a component to your
Isabelle system).

Assuming that your current directory contains the example academic paper in the
subdirectory ``Isabelle_DOF-Example-I/``, you can open it similar
to any standard Isabelle theory:

```console
isabelle jedit -l Isabelle_DOF Isabelle_DOF-Example-I/IsaDofApplications.thy
```

This will open an example of a scientific paper using the pre-compiled session
``Isabelle_DOF``, i.e., you will not be able to edit the default ontologies
defined in the ``Isabelle_DOF`` session.  If you want to edit the ontology definition, 
just open the theory file with the session ``Functional-Automata``:

```console
isabelle jedit -l Functional-Automata Isabelle_DOF-Example-I/IsaDofApplications.thy
```

While this gives you more flexibility, it might "clutter" your editing
experience, as a lot of internal theories are loaded into Isabelle's editor.

## Repository Structure

The ``main`` branch of this Repository is developed using the latest official
release of Isabelle. This is also the main development branch. In addition, he
``Isabelle_dev`` branch is used for testing Isabelle/DOF with the latest
development version of Isabelle.

This repository is structured into several Isabelle sessions, each of which is stored
in a subdirectory:

* [Isabelle_DOF](./Isabelle_DOF/): This is the main session, providing the
  Isabelle/DOF system. Furthermore, this session is currently under
  consideration for a submission to the AFP.
* [Isabelle_DOF-Example-I](./Isabelle_DOF-Example-I/):
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

## Releases

For releases, signed archives including a PDF version of the Isabelle/DOF manual
are available. The latest release is **Isabelle/DOF 1.3.0/Isabelle2021-1**:

* [Isabelle_DOF-1.3.0_Isabelle2021-1.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.pdf)
* [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz)
* [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc)

Older releases are available [here.](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/)

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
