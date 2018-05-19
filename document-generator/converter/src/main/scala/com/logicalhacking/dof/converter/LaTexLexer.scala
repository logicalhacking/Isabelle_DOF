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

package com.logicalhacking.dof.converter

import scala.util.parsing.combinator._

import scala.Left
import scala.Right

sealed trait LaTeXToken

case class  SPACING (str: String) extends LaTeXToken
case class  RAWTEXT (str: String) extends LaTeXToken
case class  COMMAND (str: String) extends LaTeXToken
case class  BEGINENV(prelude: String, str: String) extends LaTeXToken
case class  ENDENV  (prelude: String, str: String) extends LaTeXToken
case object VBACKSLASH            extends LaTeXToken  /* verbatim backslash */
case object VSPACE                extends LaTeXToken  /* verbatim space */
case object VTILDE                extends LaTeXToken  /* verbatim tilde */
case object VUNDERSCORE           extends LaTeXToken  /* verbatim underscore */
case object VCURLYOPEN            extends LaTeXToken  /* verbatim curly bracket open */
case object VCURLYCLOSE           extends LaTeXToken  /* verbatim curly bracket close */
case object VBRACKETOPEN          extends LaTeXToken  /* verbatim square bracket open */
case object VBRACKETCLOSE         extends LaTeXToken  /* verbatim square bracket close */
case object CURLYOPEN             extends LaTeXToken
case object CURLYCLOSE            extends LaTeXToken
case object BRACKETOPEN           extends LaTeXToken
case object BRACKETCLOSE          extends LaTeXToken
case object NEWLINE               extends LaTeXToken


sealed trait LaTeXCompilationError
case class LaTeXLexerError (msg: String) extends LaTeXCompilationError
case class LaTeXParserError(msg: String) extends LaTeXCompilationError


object LaTeXLexer extends RegexParsers {

  override def skipWhitespace = false  /* No skipping, we want to maintain the layout 
                                          structure of the LaTeX file */
  /* override val whiteSpace = "[ \t\r\f]+".r   -- probably not useful here */
  
  def spacing:  Parser[SPACING] = {
    "[ \t\r\f_]*".r ^^ { str => SPACING(str) }
  }
  
  def raw_text: Parser[RAWTEXT] = {
    "[^\\{\\}\\\\]+".r       ^^ { str => RAWTEXT(str) }  
               /* should recognize strings without backslash 
                  and without curly bracket { */
  }
  
  def begin0: Parser[String]   = {
               "\\\\begin[^\\{]*".r    ^^ (_.toString)   
               /* grabs whitespace and also env options ... */
  }

  def end0: Parser[String]      = {
               "\\\\end\\{.*".r      ^^ (_.toString)   
               /* grabs whitespace and also env options ... */
  }
  
  def arg: Parser[String]      = {
               "\\{[^\\}]*\\}".r       ^^ (_.toString)  
  } 
  
  def begin_env      = begin0 ~ arg    ^^ {case begin_txt ~ arg => BEGINENV(begin_txt,arg)}
  def end_env        = end0   ~ arg    ^^ {case end_txt   ~ arg => ENDENV  (end_txt,arg)}
                                 
  def command: Parser[COMMAND] = {
               "\\\\[<>a-zA-Z0-9][<>a-zA-Z0-9*]*".r ^^ { str => COMMAND(str) }
  }

  def vbackslash     = "\\\\"      ^^ (_ => VBACKSLASH    ) 
  def vspace         = "\\ "       ^^ (_ => VSPACE        )   
  def vtilde         = "\\~"       ^^ (_ => VTILDE        )   
  def vunderscore    = "\\_"       ^^ (_ => VUNDERSCORE   )   
  def vcurlyopen     = "\\{"       ^^ (_ => VCURLYOPEN    ) 
  def vcurlyclose    = "\\}"       ^^ (_ => VCURLYCLOSE   ) 
  def vbracketopen   = "\\["       ^^ (_ => VBRACKETOPEN  ) 
  def vbracketclose  = "\\]"       ^^ (_ => VBRACKETCLOSE ) 
  def newline        = "\n"        ^^ (_ => NEWLINE       ) 
  def curlyopen      = "{"         ^^ (_ => CURLYOPEN     ) 
  def curlyclose     = "}"         ^^ (_ => CURLYCLOSE    ) 
  def bracketopen    = "["         ^^ (_ => BRACKETOPEN   ) 
  def bracketclose   = "]"         ^^ (_ => BRACKETCLOSE  ) 
  
  def tokens: Parser[List[LaTeXToken]] = {
    phrase(rep1( raw_text   |
                 vbackslash | vspace       | vtilde | vunderscore |
                 vcurlyopen | vcurlyclose  | vbracketopen | vbracketclose |
                 curlyopen  | curlyclose   | bracketopen  | bracketclose  |
                 newline    | begin_env  | end_env      | command)) 
  }


  def toString(tokens: List[LaTeXToken]) : String = {
      var result = ""
        for (token <- tokens) {
            var str = token match {
              case (SPACING(spaces))   => {spaces}
              case (RAWTEXT(txt))      => {txt }
              case (COMMAND(txt))      => {txt }
              case (BEGINENV(pre,txt)) => {pre + txt}
              case (ENDENV(pre,txt))   => {pre + txt}  
              case (VBACKSLASH)        => {"""\\""" }
              case (VSPACE)            => {"""\ """ }
              case (VTILDE)            => {"""\~""" }
              case (VUNDERSCORE)       => {"""\_""" }
              case (VCURLYOPEN)        => {"""\{""" }
              case (VCURLYCLOSE)       => {"""\}""" }
              case (VBRACKETOPEN)      => {"""\[""" }
              case (VBRACKETCLOSE)     => {"""\]""" }
              case (NEWLINE)           => {"\n"     }
              case (CURLYOPEN)         => {"""{"""  }
              case (CURLYCLOSE)        => {"""}"""  }
              case (BRACKETOPEN)       => {"""["""  }
              case (BRACKETCLOSE)      => {"""]"""  }
              case (token)             =>  {"\n+++ INTERNAL ERROR +++\n"}
           }
           result += str
       }
       result
  }
  
  
  def apply(code: String): Either[LaTeXLexerError, List[LaTeXToken]] = {
         parse(tokens, code) match {
           case NoSuccess(msg, next) => Left(LaTeXLexerError(msg))
           case Success(result, next) => Right(result)
    }
  }
}
