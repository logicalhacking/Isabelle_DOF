/* Inspired from http://enear.github.io/2016/03/31/parser-combinators/ */

import scala.util.parsing.combinator._

sealed trait LaTeXToken

case class  SPACING (str: String) extends LaTeXToken
case class  RAWTEXT (str: String) extends LaTeXToken
case class  COMMAND (str: String) extends LaTeXToken
case class  BEGINENV(prelude: String, str: String) extends LaTeXToken
case class  ENDENV  (prelude: String, str: String) extends LaTeXToken
case object VBACKSLASH            extends LaTeXToken  /* verbatim backslash */
case object VCURLYOPEN            extends LaTeXToken  /* verbatim curly bracket open */
case object VCURLYCLOSE           extends LaTeXToken  /* verbatim curly bracket close */
case object VBRACKETOPEN          extends LaTeXToken  /* verbatim square bracket open */
case object VBRACKETCLOSE         extends LaTeXToken  /* verbatim square bracket close */
case object CURLYOPEN             extends LaTeXToken
case object CURLYCLOSE            extends LaTeXToken
case object BRACKETOPEN           extends LaTeXToken
case object BRACKETCLOSE          extends LaTeXToken

trait LaTeXCompilationError
case class LaTeXLexerError(msg: String) extends LaTeXCompilationError


object LaTeXLexer extends RegexParsers {

  override def skipWhitespace = false  /* No skipping, we want to maintain the layout 
                                          structure of the LaTeX file */
  /* override val whiteSpace = "[ \t\r\f]+".r   -- probably not usefule here */
  
  def spacing:  Parser[SPACING] = {
    "[ \t\r\f_]*".r ^^ { str => SPACING(str) }
  }
  
  def raw_text: Parser[RAWTEXT] = {
    "[^\\{\\}\\\\]+".r       ^^ { str => RAWTEXT(str) }        /* should recognize strings without backslash 
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
  
  def begin          = begin0 ~ arg    ^^ {case begin_txt ~ arg => BEGINENV(begin_txt,arg)}
  def end            = end0   ~ arg    ^^ {case end_txt   ~ arg => ENDENV  (end_txt,arg)}
                                 
  def command: Parser[COMMAND] = {
               "\\\\[a-zA-Z][a-zA-Z0-9*]*".r ^^ { str => COMMAND(str) }
  }

  def vbackslash     = "\\\\"      ^^ (_ => VBACKSLASH    ) 
  def vcurlyopen     = "\\{"       ^^ (_ => VCURLYOPEN    ) 
  def vcurlyclose    = "\\}"       ^^ (_ => VCURLYCLOSE   ) 
  def vbracketopen   = "\\["       ^^ (_ => VBRACKETOPEN  ) 
  def vbracketclose  = "\\]"       ^^ (_ => VBRACKETCLOSE ) 
  def curlyopen      = "{"         ^^ (_ => CURLYOPEN     ) 
  def curlyclose     = "}"         ^^ (_ => CURLYCLOSE    ) 
  def bracketopen    = "["         ^^ (_ => BRACKETOPEN   ) 
  def bracketclose   = "]"         ^^ (_ => BRACKETCLOSE   ) 
  
  def tokens: Parser[List[LaTeXToken]] = {
    phrase(rep1(raw_text   | 
                vbackslash | vcurlyopen  | vcurlyclose  | vbracketopen | vbracketclose |
                curlyopen  | curlyclose  | bracketopen  | bracketclose |            
                begin      | end         | command)) 
  }

  def printTokens(tokens: List[LaTeXToken]) : Unit = {
      tokens.headOption match {
    
        case Some(SPACING(spaces))   => {println(spaces); printTokens(tokens.tail)}
                                     
        case Some(RAWTEXT(txt))      => {println(txt); printTokens(tokens.tail)}
                                     
        case Some(COMMAND(txt))      => {println(txt); printTokens(tokens.tail)}
    
        case Some(BEGINENV(pre,txt)) => {println(pre + txt); printTokens(tokens.tail)}
                                     
        case Some(ENDENV(pre,txt))   => {println(pre + txt); printTokens(tokens.tail)}  
          
        case Some(VBACKSLASH)        => {println("\\\\"); printTokens(tokens.tail)}
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


/* Testing Zone */

>>>  LaTeXLexer("\\\\")                   => Right(List(VBACKSLASH)) // ok
>>>  LaTeXLexer("qsdqsd{dfgdfg")          => Right(List(RAWTEXT(qsdqsd), CURLYOPEN, RAWTEXT(dfgdfg))) // ok
>>>  LaTeXLexer("qsdqsd}dfgdfg")          => = Right(List(RAWTEXT(qsdqsd), CURLYCLOSE, RAWTEXT(dfgdfg))) // ok  
>>>  LaTeXLexer("qsdqsd\tdfgdfg\n\n  \n") => ... // ok
>>>  LaTeXLexer("qsdqsd\\\\dfgdfg")       => Right(List(RAWTEXT(qsdqsd), VBACKSLASH, RAWTEXT(dfgdfg))
>>>  LaTeXLexer("qsdqsd\\dfgdfg*{sdfsdf}")=> Right(List(RAWTEXT(qsdqsd), COMMAND(\dfgdfg*), CURLYOPEN, 
                                                        RAWTEXT(sdfsdf), CURLYCLOSE))  // ok
>>>  LaTeXLexer("qsdqsd\\begin ghjghj")   => Right(List(RAWTEXT(qsdqsd), COMMAND(\begin), RAWTEXT( ghjghj)))
                                             // nok


object TestLaTeXLexer extends LaTeXLexer {

  def main(args: Array[String]) = {
    parse(tokens, "johnny 121") match {
      case Success(matched,_) => println(matched)
      case Failure(msg,_) => println("FAILURE: " + msg)
      case Error(msg,_) => println("ERROR: " + msg)
    }
  }
}
