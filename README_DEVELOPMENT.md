# Isabelle/DOF: Instructions on Using the Development Version

## Pre-requisites

Isabelle/DOF has three major prerequisites:

* **Isabelle:** Isabelle/DOF requires [Isabelle 2025-2]
  (https://isabelle.in.tum.de).
* **AFP:** Isabelle/DOF requires several entries from the [development version of the Archive of Formal Proofs
  (AFP)](https://devel.isa-afp.org/).
* **LaTeX:** Isabelle/DOF requires a modern LaTeX installation, i.e., at least
  [TeX Live 2022](https://www.tug.org/texlive/) with all available updates
  applied.

### Note on Installing the AFP

Depending on your personal preference, there are two alternative approaches to
providing the necessary AFP entries for the latest official release of Isabelle.
Both have their own advantages and disadvantages.

#### Variant 1: Installing the Complete AFP

If you use the AFP with other Isabelle projects, you might want to install the
complete AFP. For this, please follow the instructions given at
<https://www.isa-afp.org/using.html>.

As Isabelle session names need to be unique, you will need to disable the entry
``Isabelle_DOF`` that is provided as part of the AFP. For doing so, you will
need to edit the file ``$AFP/thys/ROOTS`` (where ``$AFP`` refers to the
directory in which you installed the AFP) and delete the entry
``Isabelle_DOF``.

For the development version of Isabelle, installing the complete AFP
by cloning the [afp-devel](https://foss.heptapod.net/isa-afp/afp-devel/)
repository is the only supported installation method.

#### Variant 2: Installing Only the Required AFP Entries

The provided script ``install-afp`` tries to install the AFP entries that are
required by Isabelle/DOF. Note that this script will only work, if the AFP is
not registered as an Isabelle component. It can be executed as follows:

```console
foo@bar:~$ isabelle components -u .
foo@bar:~$ isabelle ./env ./install-afp
```

Note that this option is not supported for the development version of Isabelle.
If the last step crashes, it may help to add 'AFP' into the toplevel ROOTS file.

## Installation

Isabelle/DOF is provided as an Isabelle component. After installing the
prerequisites, change into the directory containing Isabelle/DOF (this should be
the directory containing this `README.md` file) and execute (if you executed
this command already during the installation of the prerequisites, you can skip
it now):

```console
foo@bar:~$ isabelle components -u .
foo@bar:~$ isabelle components -u upstream_afp
```

The final step for the installation is:

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

Overall, the use of the development version follows the description available
for the AFP version. Hence, for details please consult the Isabelle/DOF manual.

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
