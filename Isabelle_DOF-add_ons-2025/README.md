# [Isabelle/DOF 2004 Add-Ons](https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF)

Isabelle/DOF is a novel Document Ontology Framework on top of Isabelle.
Isabelle/DOF allows for both conventional typesetting and formal development.

This repository contains add-ons to the [Isabelle/DOF core
package](https://www.isa-afp.org/entries/Isabelle_DOF.html) available in the [Archive of
Formal Proofs (AFP)](https://www.isa-afp.org/). In particular, the following
add-ons are provided:

* Additional document ontologies and LaTeX templates (in the session `Isabelle_DOF-Ontologies`).
* Additional examples using various Ontologies and LaTeX template.
* A tool for creating new Isabelle/DOF projects (`isabelle dof_mkroot`).

These add-ons are provided in the archive `Isabelle_DOF-add_ons-2025.tar.xz`.
Additional, this entry contains a scaffold that allows for easily starting a new
project with the version of Isabelle/DOF provided in the AFP (i.e., without the
add ons installed). This scaffold is provided in the archive
`Isabelle_DOF-Scaffold-2025`.

## Pre-requisites

Isabelle/DOF has two major prerequisites:

* **Isabelle 2025:** Isabelle/DOF requires [Isabelle
  2025](https://isabelle.in.tum.de/), which can be obtained from the Isabelle
  homepage: <https://isabelle.in.tum.de/>.  
* **AFP (for Isabelle 2025)**: Isabelle/DOF requires several entries from the
  [Archive of Formal Proofs (AFP)](https://www.isa-afp.org/).
* **LaTeX:** Isabelle/DOF requires a modern LaTeX installation, i.e., at least
  [TeX Live 2022](https://www.tug.org/texlive/) with all available updates
  applied.
  
## Installation

### Installation of Isabelle

Please download Isabelle 2025 from the [Isabelle
Website](http://isabelle.in.tum.de/website-Isabelle2025/index.html) and follow
the system specific instructions for its installation.

### Installation from the Archive of Formal Proofs (AFP)

The core of Isabelle/DOF is available in the AFP. Hence, for using the
Isabelle/DOF Add-Ons package, please install the AFP following the instructions
given at <https://www.isa-afp.org/help.html>. In the following, we assume that
the AFP has been registered as Isabelle component.

Isabelle/DOF is provided as one AFP entry:

* [Isabelle_DOF:](https://www.isa-afp.org/entries/Isabelle_DOF.html) This entry
  contains the Isabelle/DOF system itself, including the Isabelle/DOF manual.

### Isabelle/DOF Add-Ons

Unpack the archive `Isabelle_DOF-add_ons-2025.tar.xz` and change into the 
directory containing the content of the archive. In this directory, execute
the following command to register these add-ons as Isabelle components:

```console
foo@bar:Isabelle_DOF-add_ons-2025$ isabelle components -u . 
```

for building the standard session of Isabelle/DOF, execute the following command:

```console
foo@bar:~$ isabelle build -D . -x Isabelle_DOF-Proofs -x HOL-Proofs
```

This will compile Isabelle/DOF and run the example suite.

For building the session ``Isabelle_DOF-Proofs``, the timeout might need to be
increased to avoid timeouts during building the dependencies:

```console
foo@bar:~$ isabelle build -d . -o 'timeout_scale=2' Isabelle_DOF-Proofs
```

## Usage

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

While this gives you more flexibility, it might “clutter” your editing
experience, as a lot of internal theories are loaded into Isabelle's editor.

### Creating a New Project

The DOF-plugin provides an alternative to Isabelle's ``mkroot`` command.
Isabelle projects that use DOF need to be created using

```console
foo@bar:~$ isabelle dof_mkroot
```

The ``dof_mkroot`` command takes the same parameter as the standard ``mkroot``
command of Isabelle. Thereafter, the normal Isabelle command for building
documents can be used.

Using the ``-o`` option, different ontology setups can be selected and using the
``-t`` option, different LaTeX setups can be selected. For example,

```console
foo@bar:~$ isabelle dof_mkroot -o scholarly_paper -t scrartcl
```

creates a setup using the ``scholarly_paper`` ontology and the article class from
the KOMA-Script bundle.

The help (option ``-h``) show a list of all supported ontologies and document
templates:

```console
foo@bar:~$ isabelle dof_mkroot -h

Usage: isabelle dof_mkroot [OPTIONS] [DIRECTORY]

  Options are:
    -I           init Mercurial repository and add generated files
    -h           print help
    -n NAME      alternative session name (default: directory base name)
    -o NAMES     list of ontologies, separated by blanks
                 (default: "technical_report scholarly_paper")
    -q           quiet mode: less verbosity
    -t NAME      template (default: "scrreprt-modern")

  Create session root directory for Isabelle/DOF (default: current directory).
```

## Directory Structure of the Isabelle/DOF Add-Ons Archive

The Isabelle/DOF Add-Ons Archive is structured into several Isabelle sessions, each of which is stored
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
* [Isabelle_DOF-Examples-Extra](./Isabelle_DOF-Examples-Extra/): This directory
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

* Achim D. Brucker, Idir Aït-Sadoune, Nicolas Méric, Burkhart Wolff: Parametric
  ontologies in formal software engineering. Sci. Comput. Program. 241: 103231
  (2025). [do:10.1016/j.scico.2024.103231](https://doi.org/10.1016/j.scico.2024.103231)

* Nicolas Méric: An Ontology Framework for Formal Libraries: Doctoral Thesis at
  the University Pris-Saclay. (Conception et Implémentation d'un Environnement
  d'Ontologie pour des Bibliothèques Formelles). University of Paris-Saclay,
  France, 2024. <https://tel.archives-ouvertes.fr/tel-04870527>

* Achim D. Brucker, Idir Aït-Sadoune, Nicolas Méric, Burkhart Wolff: Using Deep
  Ontologies in Formal Software Engineering. ABZ 2023: 15-32.
  [doi:10.1007/978-3-031-33163-3_2](https://doi.org/10.1007/978-3-031-33163-3_2)

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
   Procedures.](https://hal.archives-ouvertes.fr/hal-01702815/document). In ERTS 2018. <https://hal.archives-ouvertes.fr/hal-01702815>

## Upstream Repository

The upstream git repository, containing the latest development version (and the
the single source of truth), for this project is hosted at
<https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF>.
