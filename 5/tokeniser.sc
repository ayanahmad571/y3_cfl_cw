/* Class Definitions */
abstract class Rexp
case object ZERO extends Rexp                                // matches nothing
case object ONE extends Rexp                                 // matches an empty string
case class ALT(r1: Rexp, r2: Rexp) extends Rexp              // alternative
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp              // sequence
case class STAR(r: Rexp) extends Rexp                        // star









// records for extracting strings or tokens
case class RECD(x: String, r: Rexp) extends Rexp  

case class PLUS(r: Rexp) extends Rexp                        // plus, 1 or more of r
case class OPTIONAL(r: Rexp) extends Rexp                    // optional 
case class NTIMES(r: Rexp, n: Int) extends Rexp              // n times
case class UPTO(r: Rexp, m: Int) extends Rexp                // up until
case class FROM(r: Rexp, n: Int) extends Rexp                // from
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp     // between n and m but more than 0 
case class NOT(r: Rexp) extends Rexp                         // not r
case class CFUN(f: Char => Boolean) extends Rexp             // single construction, 

// values  
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Plus(vs: List[Val]) extends Val
case class Ntimes(vs: List[Val]) extends Val
case class Optional(v: Val) extends Val
case class Rec(x: String, v: Val) extends Val

abstract class Token extends Serializable 
case object T_SEMI extends Token
case object T_LPAREN_C extends Token
case object T_RPAREN_C extends Token
case object T_LPAREN_N extends Token
case object T_RPAREN_N extends Token
case class T_ID(s: String) extends Token
case class T_ID_CONST(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_STR(s: String) extends Token
case class T_CHR(s: String) extends Token

case class T_FNUM(n: Float) extends Token
case class T_TYPE(s: String) extends Token
case object T_COMMA extends Token

/* End Class Definitions */

/* CFUN translations */
def CHAR(c : Char) = CFUN((ch : Char) => c == ch)
def RANGE(s: List[Char]) = CFUN((ch : Char) => s.contains(ch))
def ALL = CFUN ((_ : Char) => true)
/* End CFUN translations */


def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}

implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}
implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

/* 
* Nullable Function 
* This tests whether a regular expression can recognize the empty string
*/
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  
  case PLUS(r) => nullable(r)
  case OPTIONAL(r) => true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
  case NOT(r) => !nullable(r)
  case RECD(_, r1) => nullable(r1)
  case CFUN(_) => false
}
/* End Nullable Function */

/* 
* Der Function 
* The derivative of a regular expression w.r.t. a character
*/
def der(c: Char, r: Rexp) : Rexp = r match {
	case ZERO => ZERO
	case ONE => ZERO
	case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
	case SEQ(r1, r2) => if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2)) else SEQ(der(c, r1), r2)
	case STAR(r1) => SEQ(der(c, r1), STAR(r1))

	case PLUS(r) => SEQ(der(c, r), STAR(r))
	case OPTIONAL(r) => der(c, r)
	case NTIMES(r, n) => if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
	case NOT(r) => NOT(der(c, r))
    case RECD(_, r1) => der(c, r1)
	case CFUN(f) => if(f(c)) ONE else ZERO
}
/* End Der Function */

// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
    case Right(v) => Right(f2(v))
    case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f1: Val => Val) = (v:Val) => v match {
    case Rec(x, v) => Rec(x, f1(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")






// simplification
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Plus(vs) => vs.map(flatten).mkString
  case Ntimes(vs) => vs.map(flatten).mkString
  case Optional(v) => flatten(v)
  case Rec(_, v) => flatten(v)
}

// extracts an environment from a value;

// used for tokenising a string
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Plus(vs) => vs.flatMap(env)
  case Ntimes(vs) => vs.flatMap(env)
  case Optional(v) => env(v)
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  // case CFUN(_) => Wont Work 
  case ALT(r1, r2) => 
      if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
 
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPTIONAL(r) => Stars(Nil)
  case NTIMES(r,n) => Stars(List.fill(n)(mkeps(r))) // Filling the list N times
  

}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  // case (CHAR(d), Empty) => Chr(c) 
  case (CFUN(_), Empty) => Chr(c)

  case (OPTIONAL(r), v) => Stars(inj(r, c, v)::Nil)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}



// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else  { println(r); throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// Question 1
val LETTERS_LIST = ('a' to 'z').toList ::: ('A' to 'Z').toList
val CAPITAL_LETTERS_LIST = ('A' to 'Z').toList

val EXTRA_CHARS_LIST : List[Char] = List('.' , '_' , '>' , '<' , '=' , ';' , '\\', ':', ',', '-'); 
val DIGITS_NO_ZERO : Rexp = RANGE(('1' to '9').toList)

val KEYWORD : Rexp = "def" | "val" | "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" | "upto" | "print_char" | "print_int" | "new_line" | "print_space" | "print_star"
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||" | "=" | ":"

val CHAR_OP: Rexp = "," | "+" | "-" | "*" | "%" | "/" | "=" | "!" | ">" | "<" | "&" | "|" | ":" 

val LETTERS : Rexp = RANGE(LETTERS_LIST)
val CAPITAL_LETTERS : Rexp = RANGE(CAPITAL_LETTERS_LIST)
val SYMBOLS : Rexp = RANGE(LETTERS_LIST ::: EXTRA_CHARS_LIST ) 
val RPAREN: Rexp = "{" | "("
val LPAREN: Rexp = "}" | ")"
val SEMI: Rexp = ";"
val COMMA: Rexp = ","
val UNDERSCORE: Rexp = "_"
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r")
val NEWLINE = PLUS("\r\n" | "\r" | "\n")
val DIGIT = RANGE(('0' to '9').toList)
val SIGNS : List[Char] = List('-', '+'); 
val PREFIXES = RANGE(SIGNS)


//Can recognise 0 but not numbers with leading 0s
val TYPES : Rexp = "Int" | "Double" | "Void" | "String" | "Float"
 
val NUMBER = ((DIGIT) | (DIGITS_NO_ZERO ~ PLUS(DIGIT)))
val DOUBLE = OPTIONAL(PREFIXES) ~ STAR(DIGIT) ~ OPTIONAL(".") ~ PLUS(DIGIT)
val ID = LETTERS ~ (UNDERSCORE | LETTERS | DIGIT).% // star or PLUS
val ID_CONST = CAPITAL_LETTERS ~ (UNDERSCORE | LETTERS | DIGIT).% // star or PLUS
val STRING: Rexp = "\"" ~ (SYMBOLS | DIGIT | WHITESPACE).% ~ "\""
val CHAR_S: Rexp = "\'" ~ (SYMBOLS | DIGIT | WHITESPACE | CHAR_OP).% ~ "\'"
val COMMENT : Rexp = "//" ~ (SYMBOLS | CHAR(' ') | DIGIT | RPAREN | LPAREN | COMMA | "//" | "\'" | "\"").% ~ NEWLINE


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("t" $ TYPES) | 
                  ("ic" $ ID_CONST) | 
                  ("i" $ ID) | 
                  ("o" $ OP) |
                  ("n" $ NUMBER) | 
                  ("d" $ DOUBLE) | 
                  ("s" $ SEMI) | 
                  ("l" $ COMMA) | 
                  ("str" $ STRING ) |
                  ("chr" $ CHAR_S) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("c" $ COMMENT) | 
                  ("w" $ WHITESPACE)).%


val token : PartialFunction[(String, String), Token] = {
  case ("s", _) => T_SEMI
  case ("l", _) => T_COMMA
  case ("p", "{") => T_LPAREN_C
  case ("p", "}") => T_RPAREN_C
  case ("p", "(") => T_LPAREN_N
  case ("p", ")") => T_RPAREN_N
  case ("i", s) => T_ID(s)
  case ("ic", s) => T_ID_CONST(s)
  case ("t", s) => T_TYPE(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("d", s) => T_FNUM(s.toFloat)
  case ("k", s) => T_KWD(s)
  case ("str", s) => T_STR(s)
  case ("chr", s) => T_CHR(s)
}

def tokenise(s: String) : List[Token] = lexing_simp(WHILE_REGS, s).collect(token)

import ammonite.ops._
//@doc("Tokenising a file.")
@main
def main(fname: String) = {
  println(tokenise(os.read(os.pwd / fname)))
}






