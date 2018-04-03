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
case object VCURLYOPEN            extends LaTeXToken  /* verbatim curly bracket open */
case object VCURLYCLOSE           extends LaTeXToken  /* verbatim curly bracket close */
case object VBRACKETOPEN          extends LaTeXToken  /* verbatim square bracket open */
case object VBRACKETCLOSE         extends LaTeXToken  /* verbatim square bracket close */
case object CURLYOPEN             extends LaTeXToken
case object CURLYCLOSE            extends LaTeXToken
case object BRACKETOPEN           extends LaTeXToken
case object BRACKETCLOSE          extends LaTeXToken

sealed trait LaTeXCompilationError
case class LaTeXLexerError (msg: String) extends LaTeXCompilationError
case class LaTeXParserError(msg: String) extends LaTeXCompilationError


object LaTeXLexer extends RegexParsers {

  override def skipWhitespace = false  /* No skipping, we want to maintain the layout 
                                          structure of the LaTeX file */
  /* override val whiteSpace = "[ \t\r\f]+".r   -- probably not usefule here */
  
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
               "\\\\end[^\\{]*".r      ^^ (_.toString)   
               /* grabs whitespace and also env options ... */
  }
  
  def arg: Parser[String]      = {
               "\\{[^\\}]*\\}".r       ^^ (_.toString)  
  } 
  
  def begin_env      = begin0 ~ arg    ^^ {case begin_txt ~ arg => BEGINENV(begin_txt,arg)}
  def end_env        = end0   ~ arg    ^^ {case end_txt   ~ arg => ENDENV  (end_txt,arg)}
                                 
  def command: Parser[COMMAND] = {
               "\\\\[a-zA-Z0-9][a-zA-Z0-9*]*".r ^^ { str => COMMAND(str) }
  }

  def vbackslash     = "\\\\"      ^^ (_ => VBACKSLASH    ) 
  def vspace         = "\\ "       ^^ (_ => VSPACE        )   
  def vtilde         = "\\~"       ^^ (_ => VTILDE        )   
  def vcurlyopen     = "\\{"       ^^ (_ => VCURLYOPEN    ) 
  def vcurlyclose    = "\\}"       ^^ (_ => VCURLYCLOSE   ) 
  def vbracketopen   = "\\["       ^^ (_ => VBRACKETOPEN  ) 
  def vbracketclose  = "\\]"       ^^ (_ => VBRACKETCLOSE ) 
  def curlyopen      = "{"         ^^ (_ => CURLYOPEN     ) 
  def curlyclose     = "}"         ^^ (_ => CURLYCLOSE    ) 
  def bracketopen    = "["         ^^ (_ => BRACKETOPEN   ) 
  def bracketclose   = "]"         ^^ (_ => BRACKETCLOSE  ) 
  
  def tokens: Parser[List[LaTeXToken]] = {
    phrase(rep1( raw_text   |
                 vbackslash | vspace       | vtilde |
                 vcurlyopen | vcurlyclose  | vbracketopen | vbracketclose |
                 curlyopen  | curlyclose   | bracketopen  | bracketclose  |
                 begin_env  | end_env      | command)) 
  }

  def printTokens(tokens: List[LaTeXToken]) : Unit = {
      tokens.headOption match {
    
        case Some(SPACING(spaces))   => {println(spaces); printTokens(tokens.tail)}
                                     
        case Some(RAWTEXT(txt))      => {println(txt); printTokens(tokens.tail)}
                                     
        case Some(COMMAND(txt))      => {println(txt); printTokens(tokens.tail)}
    
        case Some(BEGINENV(pre,txt)) => {println(pre + txt); printTokens(tokens.tail)}
                                     
        case Some(ENDENV(pre,txt))   => {println(pre + txt); printTokens(tokens.tail)}  
          
        case Some(VBACKSLASH)        => {println("\\\\"); printTokens(tokens.tail)}
        case Some(VSPACE)            => {println("\\ "); printTokens(tokens.tail)}
        case Some(VTILDE)            => {println("\\~"); printTokens(tokens.tail)}
        case Some(VCURLYOPEN)        => {println("\\{"); printTokens(tokens.tail)}
        case Some(VCURLYCLOSE)       => {println("\\}"); printTokens(tokens.tail)}
        case Some(VBRACKETOPEN)      => {println("\\["); printTokens(tokens.tail)}
        case Some(VBRACKETCLOSE)     => {println("\\]"); printTokens(tokens.tail)}
        case Some(CURLYOPEN)         => {println("{"); printTokens(tokens.tail)}
        case Some(CURLYCLOSE)        => {println("}"); printTokens(tokens.tail)}
        case Some(BRACKETOPEN)       => {println("["); printTokens(tokens.tail)}
        case Some(BRACKETCLOSE)      => {println("]"); printTokens(tokens.tail)}
             
        case Some(token)             =>  {println("+++ INTERNAL ERROR +++"); 
                                          printTokens(tokens.tail)}
    
        case None => {println("\n\n")}  
      }
  }

  def apply(code: String): Either[LaTeXLexerError, List[LaTeXToken]] = {
         parse(tokens, code) match {
           case NoSuccess(msg, next) => Left(LaTeXLexerError(msg))
           case Success(result, next) => Right(result)
    }
  }
}
