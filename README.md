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
the directory containing this `README.md` file) and execute (if you executed
this command already during the installation of the prerequisites, you can skip
it now):

```console
foo@bar:~$ isabelle components -u .
```

The final step for the installation is:

```console
foo@bar:~$ isabelle build -D . -x Isabelle_DOF-proofs
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
``Isabelle_DOF``, i.e., you will not be able to edit the ontology definitions.
If you want to edit the ontology definition, just open the theory file with the
default HOL session:

```console
isabelle jedit -d . -l HOL Isabelle_DOF-Example-Scholarly_Paper/IsaDofApplications.thy
```

While this gives you more flexibility, it might "clutter" your editing
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

creates a setup using the scholarly_paper ontology and the article class from
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

## Releases

For releases, signed archives including a PDF version of the Isabelle/DOF manual
are available:

* Isabelle/DOF 1.3.0/Isabelle2021-1
  * [Isabelle_DOF-1.3.0_Isabelle2021-1.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.pdf)
  * [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz)
  * [Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.3.0_Isabelle2021-1.tar.xz.asc)

### Older Releases

* Isabelle/DOF 1.2.0/Isabelle2021
  * [Isabelle_DOF-1.2.0_Isabelle2021.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.2.0_Isabelle2021.pdf)
  * [Isabelle_DOF-1.2.0_Isabelle2021.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.2.0_Isabelle2021.tar.xz)
  * [Isabelle_DOF-1.2.0_Isabelle2021.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.2.0_Isabelle2021.tar.xz.asc)
* Isabelle/DOF 1.1.0/Isabelle2021
  * [Isabelle_DOF-1.1.0_Isabelle2021.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2021.pdf)
  * [Isabelle_DOF-1.1.0_Isabelle2021.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2021.tar.xz)
  * [Isabelle_DOF-1.1.0_Isabelle2021.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2021.tar.xz.asc)
* Isabelle/DOF 1.1.0/Isabelle2020
  * [Isabelle_DOF-1.1.0_Isabelle2020.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2020.pdf)
  * [Isabelle_DOF-1.1.0_Isabelle2020.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2020.tar.xz)
  * [Isabelle_DOF-1.1.0_Isabelle2020.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.1.0_Isabelle2020.tar.xz.asc)
* Isabelle/DOF 1.0.0/Isabelle2019
  * [Isabelle_DOF-1.0.0_Isabelle2019.pdf](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.0.0_Isabelle2019.pdf)
  * [Isabelle_DOF-1.0.0_Isabelle2019.tar.xz](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.0.0_Isabelle2019.tar.xz)
  * [Isabelle_DOF-1.0.0_Isabelle2019.tar.xz.asc](https://artifacts.logicalhacking.com/releases/Isabelle_DOF/Isabelle_DOF/Isabelle_DOF-1.0.0_Isabelle2019.tar.xz.asc)

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
