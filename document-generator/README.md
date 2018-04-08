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
isabelle DOF_mkroot -d 
```
The ``DOF_mkroot`` command takes the same parameter as the standard
``mkroot`` command of Isabelle. Thereafter, the normal Isabelle 
command for building documents can be used. 

## License

This project is licensed under a 2-clause BSD license.

SPDX-License-Identifier: BSD-2-Clause
