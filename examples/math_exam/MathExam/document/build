#!/usr/bin/env bash
# Copyright (c) 2018-2019 The University of Sheffield. All rights reserved.
#               2018 The University of Paris-Sud. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in
#    the documentation and/or other materials provided with the
#    distribution.
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
# FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
# COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
# INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
# BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
# ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
#
# SPDX-License-Identifier: BSD-2-Clause

OUTFORMAT=${1:-pdf}
NAME=${2:-root}

set -e

ROOT_NAME="root_$NAME"
[ ! -f "$DIR/$ROOT_NAME.tex" ] && ROOT_NAME="root"

if [ ! -f $ISABELLE_HOME_USER/DOF/latex/DOF-core.sty ]; then
    echo ""
    echo "Error: Isabelle/DOF not installed"
    echo "====="
    echo "This is a Isabelle/DOF project. The document preparation requires"
    echo "the Isabelle/DOF framework. Please obtain the framework by cloning"
    echo "the Isabelle/DOF git repository, i.e.: "
    echo "    git clone https://git.logicalhacking.com/HOL-OCL/Isabelle_DOF"
    echo "You can install the framework as follows:"
    echo "    cd Isabelle_DOF/document-generator"
    echo "    ./install"
    echo ""
    exit 1
fi

if [ ! -f root.inf ]; then 
    echo ""
    echo "Error: Isabelle/DOF document setup not correct"
    echo "====="
    echo "Could not find root.inf. Please upgrade your Isabelle/DOF document"
    echo "setup manually."
    exit 1
fi

ROOT="$ISABELLE_HOME_USER/DOF/document-template/root-$(cat root.inf).tex"
if [ ! -f $ROOT]; then 
    echo ""
    echo "Error: Isabelle/DOF document setup not correct"
    echo "====="
    echo "Could not find root file ($ROOT)."
    echo "Please upgrade your Isabelle/DOF document setup manually."
    exit 1
fi

cp $ROOT root.tex
cp $ISABELLE_HOME_USER/DOF/latex/*.sty .
cp $ISABELLE_HOME_USER/DOF/latex/*.sty .

$ISABELLE_TOOL latex -o sty "$ROOT_NAME.tex" && \
$ISABELLE_TOOL latex -o "$OUTFORMAT" "$ROOT_NAME.tex" && \
{ [ ! -f "$ROOT_NAME.bib" ] || $ISABELLE_TOOL latex -o bbl "$ROOT_NAME.tex"; } && \
{ [ ! -f "$ROOT_NAME.idx" ] || $ISABELLE_TOOL latex -o idx "$ROOT_NAME.tex"; } && \
$ISABELLE_TOOL latex -o "$OUTFORMAT" "$ROOT_NAME.tex" && \
$ISABELLE_TOOL latex -o "$OUTFORMAT" "$ROOT_NAME.tex"

