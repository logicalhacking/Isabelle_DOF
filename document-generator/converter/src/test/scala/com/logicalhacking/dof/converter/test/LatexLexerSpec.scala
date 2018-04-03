/**
 * Copyright (c) 2018 The University of Sheffield. All rights reserved.
 *               2018 The University of Paris-Sud. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

package com.logicalhacking.dof.converter.test

import org.scalatest._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import com.logicalhacking.dof.converter._


@RunWith(classOf[JUnitRunner])
class LatexLexerSpec extends FlatSpec with Matchers{
  
  behavior of "Parsing simple commands"
  
    it should """accept \\ as newline (VBACKSLASH)""" in {
      assert(
          LaTeXLexer("""\\""") 
          == 
          Right(List(VBACKSLASH))
      ) 
    }
  
  behavior of "Parsing section commands"
  
    it should """accept  simple section specifications""" in {
      assert(
          LaTeXLexer("""\section{title}""")
          ==
          Right(List(COMMAND("""\section"""), CURLYOPEN, RAWTEXT("title"), CURLYCLOSE))
      )
    }
  
    it should """accept star variant of section specifications""" in {
      assert(
          LaTeXLexer("""\section*{title}""") 
          == 
          Right(List(COMMAND("""\section*"""), CURLYOPEN, RAWTEXT("""title"""), CURLYCLOSE))
      ) 
    }
    
  behavior of "Parsing environments"
  
    it should "accept simple environments with arguments" in {
      assert(
          LaTeXLexer("""\begin{foo}{argument}bar\end{foo}""") 
          == 
          Right(List(BEGINENV("""\begin""","""{foo}"""), CURLYOPEN, RAWTEXT("""argument"""), 
                     CURLYCLOSE, RAWTEXT("""bar"""), ENDENV("""\end""","""{foo}""")))
      )
    }

    it should "parse simple environments with optional arguments" in {
      assert(
          LaTeXLexer("""\begin{foo}[optional] bar \end{foo}""")
          == 
          Right(List(BEGINENV("""\begin""","""{foo}"""), RAWTEXT("""[optional] bar """), ENDENV("""\end""","""{foo}""")))
      )
    }

    it should "parse simple environments optional and required arguments" in {
      assert(
          LaTeXLexer("""\begin{foo}[optional]{argument} bar \end{foo}""")
          ==
          Right(List(BEGINENV("""\begin""","""{foo}"""), RAWTEXT("""[optional]"""), CURLYOPEN, RAWTEXT("""argument"""), CURLYCLOSE, RAWTEXT(""" bar """), ENDENV("""\end""","""{foo}""")))
      )
    }

    it should "parse environments with complex arguments" in {
      assert(
          LaTeXLexer("""\begin{altenv}<2>{(}{)}{[}{]}word\end{altenv}""")
          == 
          Right(List(BEGINENV("""\begin""","""{altenv}"""), RAWTEXT("""<2>"""), CURLYOPEN, RAWTEXT("""("""), CURLYCLOSE, CURLYOPEN, RAWTEXT(""")"""), CURLYCLOSE, CURLYOPEN, RAWTEXT("""["""), CURLYCLOSE, CURLYOPEN, RAWTEXT("""]"""), CURLYCLOSE, RAWTEXT("""word"""), ENDENV("""\end""","""{altenv}""")))
      )
  }

}
