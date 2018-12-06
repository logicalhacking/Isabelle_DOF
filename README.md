# Isabelle/DOF: Document Preparation Setup

Isabelle/DOF is a novel Document Ontology Framework on top of
Isabelle. Isabelle/DOF allows for both conventional typesetting as
well as formal development.

## Installation 

In most case, the DOF-plugin can be installed as follows:
```console 
foo@bar:~$ ./install
```
If a specific Isabelle version should be used (i.e., not the default 
one), the full path to the ``isabelle`` command needs to be passed as 
argument to the ``install`` script:
```console 
foo@bar:~$ ./install /usr/local/Isabelle2017/bin/isabelle
```

The DOF-plugin will be installed in the Isabelle user directory 
(the exact location depends on the Isabelle version). 

Additionally, you have to replace the file 
```Isabelle2017/src/Pure/Thy/thy_output.ML```
by the file you find in the Isabelle_DOF-distribution:
```patches/thy_output.ML```
When starting up, Isabelle will recompile itself and integrating this 
file (which modifies about 10 lines in the LaTeX generator...).

## Usage

The DOF-plugin provides an alternative to Isabelle's ``mkroot`` command.
Isabelle projects that use DOF need to be created using
```console 
foo@bar:~$ isabelle DOF_mkroot -d 
```
The ``DOF_mkroot`` command takes the same parameter as the standard
``mkroot`` command of Isabelle. Thereafter, the normal Isabelle 
command for building documents can be used. 

Using the ``-o`` option, different ontology setups can be
selected and using the ``-t`` option, different LaTeX setups 
can be selected (use ``-h`` to obtain a list of all installed setups):
```console 
foo@bar:~$ isabelle DOF_mkroot -h

Usage: isabelle DOF_mkroot [OPTIONS] [DIR]

  Options are:
    -h           print this help text and exit
    -d           enable document preparation
    -n NAME      alternative session name (default: DIR base name)
    -o ONTOLOGY  (default: core)
       Available ontologies:
       * cenelec_50126
       * core
       * mathex
       * scholarly_paper
    -t TEMPLATE   (default: DEFAULT_TEMPLATE)
       Available document templates:
       * lncs
       * scrreprt

  Prepare session root DIR (default: current directory).
```
For example, 
```console 
foo@bar:~$ isabelle DOF_mkroot -d -o scholarly_paper -t lncs
```
creates a setup using the scholarly_paper ontology and Springer's
LNCS LaTeX class as document class. Note that the generated setup
does not include the actual ``llncs.cls`` file. This is due to
license restrictions. You need to obtain the file from Springer's
website and either copy it in you ``texmf`` directory or the ``root``
folder. In the latter case, you also need to add it in the ``ROOT`` file
as dependency.

## Team

Main contacts:
* [Achim D. Brucker](http://www.brucker.ch/)
* [Burkhart Wolff](https://www.lri.fr/~wolff/)


### Contributors

* Idir Ait-Sadoune 
* Paolo Crisafulli 
* Chantal Keller



## License

This project is licensed under a 2-clause BSD license.

SPDX-License-Identifier: BSD-2-Clause

## Publications

* Achim D. Brucker, Idir Ait-Sadoune, Paolo Crisafulli, and Burkhart
  Wolff. Using The Isabelle Ontology Framework: Linking the Formal
  with the Informal. In Conference on Intelligent Computer Mathematics
  (CICM). Lecture Notes in Computer Science, Springer-Verlag, 2018.
