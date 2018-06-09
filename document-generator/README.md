# Isabelle_DOF: Document Preparation Setup

This directory contains the DOF-plugin for Isabelle's 
document generation system. 

## Installation 

In most case, the DOF-plugin can be installed as follows:
```console 
foo@bar:~$ ./install
```
If a specific Isabelle version should be used (i.e., not the default 
one), the full path to the ``isabelle`` command needs to be passed as 
argument to the ``install`` script:
```console 
foo@bar:~$ ./install /usr/local/Isabelle2016-1/bin/isabelle
```

The DOF-plugin will be installed in the Isabelle user directory 
(the exact location depends on the Isabelle version). 

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


## Development Setup

Compilation using the provided ``build`` script, e.g.: 
```console
foo@bar:~$ cd converter
foo@bar:~$ ./build
```
This build script requires a basic Unix-environment as, e.g., provided
by Isabelle as well as a running Isabelle installation. 

In addition, a maven setup is maintained that, e.g., can be imported
into Eclipse. This results in an Scala development environment that
supports the usual features of a modern IDE, e.g., Intellisense. 

### Prerequisites (Eclipse Setup)

* Java 8
* Eclipse Oxygen, including
  * [Scala IDE and Scalatest Runner (the latter is optional)](http://download.scala-ide.org/sdk/lithium/e47/scala212/stable/site)
  * ["Maven for Scala" - Maven Integration for Eclipse](http://alchim31.free.fr/m2e-scala/update-site)

### Checkout

The converter is part of the Isabelle DOF repository:
```console
foo@bar:~$ git clone https://git.logicalhacking.com/HOL-OCL/Isabelle_DOF.git
```

### Importing the Project into Eclipse

The project  can be imported into a fresh Eclipse workspace using 
`File -> Import -> Maven -> Existing Maven Projects`. Please select
the ``converter`` directory as parent directory. After the import, you
might need to resolve the dependencies using the maven integration of 
Eclipse.

## Team

Main contacts:
* [Achim D. Brucker](http://www.brucker.ch/)
* [Burkhart Wolff](https://www.lri.fr/~wolff/)

## License

This project is licensed under a 2-clause BSD license.

SPDX-License-Identifier: BSD-2-Clause
