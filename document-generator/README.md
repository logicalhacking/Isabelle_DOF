# Isabelle_DOF: Document Preparation Setup

This directory contains the DOF-plugin for Isabelle's 
document generation system. 

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
