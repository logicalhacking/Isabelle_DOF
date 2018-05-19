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

import java.io.{ BufferedWriter, File, FileWriter }
import IoUtils._
import scala.util.matching.Regex
import scala.annotation.tailrec

object DofConverter {
  val version = "0.0.1"
  val sep=RAWTEXT("%\n")
    
  def deMarkUpArgList(tokens: List[LaTeXToken]): List[LaTeXToken] = {
    @tailrec 
    def deMarkUpArgListRec(acc:List[LaTeXToken], tokens: List[LaTeXToken]): List[LaTeXToken] = {
      val (t,tail) = tokens match {
         case CURLYOPEN :: COMMAND("""\isacharprime""") :: CURLYCLOSE :: CURLYOPEN :: COMMAND("""\isacharprime""") :: CURLYCLOSE :: tail      
          => (RAWTEXT(""),tail)
        case CURLYOPEN :: COMMAND("""\isachardoublequoteopen""") :: CURLYCLOSE :: tail  => (RAWTEXT("""{"""),tail)
        case CURLYOPEN :: COMMAND("""\isachardoublequoteclose""") :: CURLYCLOSE :: tail  => (RAWTEXT("""}"""), tail)
        case t :: tail => (t,tail)
        case Nil => (RAWTEXT(""),Nil)
      }  
      if (tokens == Nil) acc
      else deMarkUpArgListRec(acc++List(t), tail)
    }
    deMarkUpArgListRec(Nil, tokens)
  }

  def deMarkUp(tokens: List[LaTeXToken]): List[LaTeXToken] = {
    @tailrec 
    def deMarkupRec(out:List[LaTeXToken], tokens: List[LaTeXToken]): List[LaTeXToken] = {
      val (t,tail) = tokens match {
        case CURLYOPEN :: COMMAND("""\isacharcolon""") :: CURLYCLOSE :: tail      => (RAWTEXT(""":"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharunderscore""") :: CURLYCLOSE :: tail => (RAWTEXT("""_"""),tail)
        case CURLYOPEN :: COMMAND("""\isadigit""") :: CURLYOPEN::n::CURLYCLOSE::CURLYCLOSE :: tail => (n,tail)
        case CURLYOPEN :: COMMAND("""\isacharcomma""") :: CURLYCLOSE :: tail      => (RAWTEXT(""","""),tail)
        case COMMAND("""\isanewline""") :: tail                                   =>  (RAWTEXT(""),tail)
        case CURLYOPEN :: COMMAND("""\isachardot""") :: CURLYCLOSE :: tail        => (RAWTEXT("""."""),tail)
        case CURLYOPEN :: COMMAND("""\isacharsemicolon""") :: CURLYCLOSE :: tail  => (RAWTEXT(""";"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharbackslash""") :: CURLYCLOSE :: tail  => (RAWTEXT("""\"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharslash""") :: CURLYCLOSE :: tail      => (RAWTEXT("""/"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharbraceleft""") :: CURLYCLOSE :: tail  => (RAWTEXT("""{"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharbraceright""") :: CURLYCLOSE :: tail => (RAWTEXT("""}"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharparenleft""") :: CURLYCLOSE :: tail  => (RAWTEXT("""("""),tail)
        case CURLYOPEN :: COMMAND("""\isacharparenright""") :: CURLYCLOSE :: tail => (RAWTEXT(""")"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharequal""") :: CURLYCLOSE :: tail      => (RAWTEXT("""="""),tail)
        case CURLYOPEN :: COMMAND("""\isacharminus""") :: CURLYCLOSE :: tail      => (RAWTEXT("""-"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharplus""") :: CURLYCLOSE :: tail      => (RAWTEXT("""+"""),tail)
        case CURLYOPEN :: COMMAND("""\isacharprime""") :: CURLYCLOSE :: tail      => (RAWTEXT("""'"""),tail)
        case VSPACE :: tail => (RAWTEXT(""" """),tail)
        case t :: tail => (t,tail)
        case Nil => (RAWTEXT(""" """),Nil)
      }
      if (tokens == Nil) out
      else deMarkupRec(out++List(t), tail)
    }
    deMarkupRec(Nil, tokens)
  }
  
  
  def convertIsaDofCommand(cmd: String, tokens: List[LaTeXToken]): List[LaTeXToken] = {
    @tailrec 
    def convertType(head: List[LaTeXToken], tail: List[LaTeXToken]): Tuple2[String,List[LaTeXToken]] = {
      @tailrec 
      def split(head:List[LaTeXToken], tokens: List[LaTeXToken]):Tuple2[List[LaTeXToken], List[LaTeXToken]] = {
        tokens match {
          case CURLYOPEN::COMMAND("""\isacharcomma""")::CURLYCLOSE::tail => (head,tokens)          
          case CURLYCLOSE::COMMAND("""\isacharcomma""")::CURLYOPEN::tail => (head++(CURLYCLOSE::COMMAND("""\isacharcomma""")::CURLYOPEN::List()),tail)          
          case CURLYCLOSE::COMMAND("""\isacharbrackleft""")::CURLYOPEN::tail => (head++(CURLYCLOSE::COMMAND("""\isacharbrackleft""")::CURLYOPEN::List()),tail)          
          case BRACKETOPEN::tail => (head,BRACKETOPEN::tail)          
          case CURLYOPEN::COMMAND("""\isacharbrackright""")::CURLYCLOSE::tail => (head,tokens)
          case t::tail => split(head++List(t), tail)
          case t => (head,t)
        }
      }
      
      tail match {
        case CURLYOPEN::COMMAND("""\isacharcolon""")::CURLYCLOSE :: CURLYOPEN::COMMAND("""\isacharcolon""")::CURLYCLOSE :: tail => {
          val (label, shead)= split(List(), head.reverse)
          val (typ, stail) = split(List(), tail)
          val typstring = typ match {
            case RAWTEXT(s)::Nil => s.capitalize
            case _          => ""
          }
          (typstring,(shead.reverse)++List(RAWTEXT("""label={"""))++(label.reverse)++List(RAWTEXT("""}, type={"""))++typ++List(RAWTEXT("""}"""))++stail)
        }
        case t::tail => convertType(head++List(t), tail)
        case t => ("",t)
      }
    }


    @tailrec 
    def delSpace(tokens: List[LaTeXToken]): List[LaTeXToken] = {
      tokens match {
        case VSPACE :: tail => delSpace(tail)
        case COMMAND("""\isanewline""")::tail => delSpace(tail)
        case COMMAND("""\newline""")::tail => delSpace(tail)
        case RAWTEXT(""" """)::tail => delSpace(tail)    
        case RAWTEXT("\n")::tail => delSpace(tail)    
        case RAWTEXT("\t")::tail => delSpace(tail)    
        case VBACKSLASH::tail => delSpace(tail)    
        case tokens => tokens
      }
    }

    
    def backSpace(tokens: List[LaTeXToken]): List[LaTeXToken] = (delSpace(tokens.reverse)).reverse
    
    def parseIsaDofCmd(args: List[LaTeXToken], tokens: List[LaTeXToken]): Tuple3[String,List[LaTeXToken], List[LaTeXToken]] = {
      (args, tokens) match {
        case (args, COMMAND("""\isamarkupfalse""") :: tail) => parseIsaDofCmd(args, tail)
        case (args, CURLYOPEN :: COMMAND("""\isachardoublequoteopen""") :: CURLYCLOSE :: CURLYOPEN :: COMMAND("""\isacharbrackleft""") :: CURLYCLOSE :: tail) 
                             => parseIsaDofCmd(backSpace(args) ++ List(CURLYOPEN), tail)
        case (args, CURLYOPEN :: COMMAND("""\isacharbrackright""") :: CURLYCLOSE :: CURLYOPEN :: COMMAND("""\isachardoublequoteclose""") :: CURLYCLOSE :: tail) 
                             => parseIsaDofCmd(backSpace(args) ++ List(CURLYCLOSE), delSpace(tail))
        case (args, CURLYOPEN :: COMMAND("""\isacharbrackleft""") :: CURLYCLOSE :: tail) => parseIsaDofCmd(backSpace(args) ++List(sep) ++ List(BRACKETOPEN), tail)
        case (args, CURLYOPEN :: COMMAND("""\isacharbrackright""") :: CURLYCLOSE :: tail) => {
          val (typ,arglist) = convertType(List(), args)
          val (_, t1, t2)   = parseIsaDofCmd(deMarkUpArgList(arglist)++List(BRACKETCLOSE,sep), tail)
          (typ,t1,t2)
        }
        case (args, CURLYOPEN :: COMMAND("""\isacharverbatimopen""") :: CURLYCLOSE ::tail) => parseIsaDofCmd(args ++ List(CURLYOPEN), delSpace(tail))
        case (args, CURLYOPEN :: COMMAND("""\isacharverbatimclose""") :: CURLYCLOSE :: tail) => ("",deMarkUp(backSpace(args) ++ List(CURLYCLOSE)), sep::delSpace(tail))
        case (args, CURLYOPEN :: COMMAND("""\isacartoucheopen""") :: CURLYCLOSE ::tail) => parseIsaDofCmd(args ++ List(CURLYOPEN), delSpace(tail))
        case (args, CURLYOPEN :: COMMAND("""\isacartoucheclose""") :: CURLYCLOSE :: tail) => ("",deMarkUp(backSpace(args) ++ List(CURLYCLOSE)), sep::delSpace(tail))
        case (args, t :: tail) => parseIsaDofCmd(args ++ List(t), tail)
        case (args, Nil) => ("",deMarkUp(args), Nil)
      }
    }
    
    val (pre, tail) = cmd match {
      case """chapter""" => {
        val (typ,sectionArgs, tail) = parseIsaDofCmd(Nil, tokens)
        (sep::COMMAND("""\isaDofChapter"""+typ) :: sectionArgs,tail)
      }
      case """section""" => {
        val (typ,sectionArgs, tail) = parseIsaDofCmd(Nil, tokens)
        (sep::COMMAND("""\isaDofSection"""+typ) :: sectionArgs, tail)
      }
      case """subsection""" => {
        val (typ,sectionArgs, tail) = parseIsaDofCmd(Nil, tokens)
        (COMMAND("""\isaDofSubSection"""+typ) :: sectionArgs, tail)
      }
      case """subsubsection""" => {
        val (typ,sectionArgs, tail) = parseIsaDofCmd(Nil, tokens)
        (sep::COMMAND("""\isaDofSubSubSection"""+typ) :: sectionArgs, tail)
      }
      case """paragraph""" => {
        val (typ,sectionArgs, tail) = parseIsaDofCmd(Nil, tokens)
        (sep::COMMAND("""\isaDofParagraph"""+typ) :: sectionArgs, tail)
      }
      case """text""" => {
        val (typ,dofText, tail) = parseIsaDofCmd(Nil, tokens)
        (sep::COMMAND("""\isaDofText"""+typ) :: dofText, tail)
      }
      case s => (sep::COMMAND("""\isaDofUnknown{""" + s + """}""")::sep::Nil, tokens)
    }
    pre ++ convertLaTeXTokenStream(tail)
  }

  def convertLaTeXTokenStream(tokens: List[LaTeXToken]): List[LaTeXToken] = {
    @tailrec  
    def convertLaTeXTokenStreamRec(acc:List[LaTeXToken], tokens: List[LaTeXToken]): List[LaTeXToken] = {
      val (pre, tail) = tokens match {
        case Nil => (Nil, Nil)
        case COMMAND("""\isacommand""") :: CURLYOPEN :: RAWTEXT(cmd) :: CURLYOPEN
          :: COMMAND("""\isacharasterisk""") :: CURLYCLOSE :: CURLYCLOSE :: ts => (convertIsaDofCommand(cmd, ts), Nil)
        case t :: ts => (t::Nil,ts)
      }
      if (tail == Nil) pre
      else convertLaTeXTokenStreamRec(acc++pre, tail)
    }
    convertLaTeXTokenStreamRec(Nil, tokens)
  }

  def convertLaTeX(string: String): Either[LaTeXLexerError, String] = {
    LaTeXLexer(string) match {
      case Left(err) => Left(err)
      case Right(tokens) => Right(LaTeXLexer.toString(convertLaTeXTokenStream(tokens)))
    }
  }

  def convertFile(f: File): Option[(String, LaTeXLexerError)] = {
    val texFileName = f.getAbsolutePath()
    println("DOF Converter: converting " + texFileName
      + " (Not yet fully implemented!)")
    f.renameTo(new File(texFileName + ".orig"))

    using(io.Source.fromFile(texFileName + ".orig")) {
      inputFile =>
        using(new BufferedWriter(new FileWriter(new File(texFileName), true))) {
          outputFile =>
            outputFile.write("% This file was modified by the DOF LaTeX converter, version " + version + "\n")
            val input = inputFile.getLines.reduceLeft(_ + "\n" + _)

            convertLaTeX(input) match {
              case Left(err) => Some((texFileName, err))
              case Right(output) => {
                outputFile.write(output)
                None
              }
            }
        }
    }
  }

  def processArgs(args: List[String]): Option[List[String]] = {
    def printVersion() = {
      println("DOF LaTeX converter version " + version)
    }
    def printUsage() = {
      println("Usage:")
      println("    scala dof_latex_converter.jar [OPTIONS] [directory ...]")
      println("")
      println("Options:")
      println("      --version, -v    print version and exit")
      println("      --help,    -h    print usage inforamtion and exit")
    }
    args match {
      case Nil => Some(List[String]())
      case "-v" :: Nil =>
        printVersion(); None
      case "--version" :: Nil =>
        printVersion(); None
      case "-h" :: tail =>
        printUsage(); None
      case "--help" :: tail =>
        printUsage(); None
      case file :: tail => processArgs(tail) match {
        case Some(files) => Some(file :: files)
        case None => None
      }
      case _ => printUsage(); None
    }
  }

  def main(args: Array[String]): Unit = {
    val directories = processArgs(args.toList) match {
      case None =>
        System.exit(1); List[String]()
      case Some(Nil) => List[String](".")
      case Some(l) => l
    }

    val texFiles = directories.map(dir => recursiveListFiles(new File(dir), new Regex("\\.tex$"))
      .filterNot(_.length() == 0)).flatten

    println(texFiles)
    val errors = texFiles.map(file => convertFile(file)).flatten
    if (!errors.isEmpty) {
      println()
      println("DOF LaTeX converter error(s):")
      println("=============================")
      errors.map { case (file: String, err: LaTeXLexerError) => println(file + ": " + err) }
      System.exit(1)
    }
    System.exit(0)
  }
}
