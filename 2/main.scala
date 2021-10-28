
// A simple lexer inspired by work of Sulzmann & Lu
//==================================================

/* 
 * Author: Ayan Ahmad
*/

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
case class Rec(x: String, v: Val) extends Val
   
/* End Class Definitions */

def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}


/* CFUN translations */
def CHAR(c : Char) = CFUN((ch : Char) => c == ch)
def RANGE(s: Set[Char]) = CFUN((ch : Char) => s.contains(ch))
def ALL = CFUN ((_ : Char) => true)
/* End CFUN translations */

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
  case UPTO(r, _) => true
  case FROM(r, n) => if (n == 0) true else nullable(r)
  case BETWEEN(r, n, _) => if (n == 0) true else nullable(r) 
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
	case UPTO(r, m) => if (m <= 0) ZERO else SEQ(der(c, r), UPTO(r, m - 1)) // less than = is used for capping Between's 0 case
	case FROM(r, n) => if (n == 0) SEQ(der(c, r), FROM(r, n)) else SEQ(der(c, r), FROM(r, n - 1))
	case BETWEEN(r, n, m) => if (n == 0) SEQ(der(c, r), UPTO(r, m - 1 )) else SEQ(der(c, r), BETWEEN(r, n - 1, m - 1)) // if n = 0, then it is same as upto
	case NOT(r) => NOT(der(c, r))
    case RECD(_, r1) => der(c, r1)
	case CFUN(f) => if(f(c)) ONE else ZERO
}
/* End Der Function */



/* Simplification Function */
def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}
/* End Simplification Function */

/*
* Ders Function
*/
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}
/* End Multiple Ders Function */

// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = nullable(ders(s.toList, r))


// extracts a string from a value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
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
  case Rec(x, v) => (x, flatten(v))::env(v)
}


// The injection and mkeps part of the lexer
//===========================================

def mkeps(r: Rexp) : Val = r match {
    case ONE => Empty
    case ALT(r1, r2) => 
        if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
    case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
    case STAR(r) => Stars(Nil)
    case RECD(x, r) => Rec(x, mkeps(r))
    case PLUS(r) => mkeps(SEQ(r, STAR(r)));
    case OPTION(r) => Empty
    case NTIMES(r ,n) => if (n != 0) mkeps(STAR(NTIMES(r,n-1))) else Stars(Nil)

    case PLUS(r) => Sequ(mkeps(r), mkeps(STAR(r))) // r{+} = r ~ r.%
    case OPTIONAL(r) => mkeps(r) // r + 1 ? Check for case where r is nullable
    case NTIMES(r, n) => Stars(List.tabulate(n)(_ => mkeps(r)))
    case RECD(x, r) => Rec(x, mkeps(r))

}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

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

// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = 
  env(lex_simp(r, s.toList))


// The Lexing Rules for the WHILE Language

def PLUS(r: Rexp) = r ~ r.%

def Range(s : List[Char]) : Rexp = s match {
  case Nil => ZERO
  case c::Nil => CHAR(c)
  case c::s => ALT(CHAR(c), Range(s))
}
def RANGE(s: String) = Range(s.toList)

// Question 1
val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" 
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||"
val LETTERS_LIST = ('a' to 'z').toList ::: ('A' to 'Z').toList
val LETTERS : Rexp = RANGE(LETTERS_LIST)
val EXTRA_CHARS_LIST = ["." , "_" , ">" , "<" , "=" , ";" , "\\", ":"]; 
val SYM : Rexp = RANGE(LETTERS_LIST ::: EXTRA_CHARS_LIST)
val RPAREN: Rexp = "{" | "("
val LPAREN: Rexp = "}" | ")"
val SEMI: Rexp = ";"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val ID = SYM ~ (SYM | DIGIT).% 

val DIGIT = RANGE(('0' to '9').toList)
val DIGITS_NO_ZERO : Rexp = RANGE("123456789".toSet)

//Can recognise 0 but not numbers with leading 0s
val NUMBER = DIGIT | DIGITS_NO_ZERO ~ PLUS(DIGIT)

val STRING: Rexp = "\"" ~ (SYM | DIGIT | WHITESPACE).% ~ "\""



val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("w" $ WHITESPACE)).%


