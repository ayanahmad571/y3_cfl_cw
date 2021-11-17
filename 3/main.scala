
// A simple lexer inspired by work of Sulzmann & Lu
//==================================================

/* 
 * Author: Ayan Ahmad
 * K-Number: K19002255
 * Email: ayan.ahmad@kcl.ac.uk
*/

// Copied Coursework 1 and 2 code

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
case class T_OP(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_KWD(s: String) extends Token
case class T_STR(s: String) extends Token
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
 
  case PLUS(_) => Plus(Nil)
  case OPTIONAL(r) => 
    if (nullable(r)) Optional(mkeps(r)) else Optional(Empty) // Checking for the case where r is nullable
  case NTIMES(r,n) => Ntimes(List.fill(n)(mkeps(r))) // Filling the list N times
  

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

  case (OPTIONAL(r), v) => Optional(inj(r, c, v))
  case (PLUS(r), Sequ(v1, Stars(vs))) => Plus(inj(r, c, v1)::vs)
  case (NTIMES(r, n), Sequ(v1, Ntimes(vs))) => Ntimes(inj(r, c, v1)::vs)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}



// lexing functions including simplification
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else  { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// Question 1
val LETTERS_LIST = ('a' to 'z').toList ::: ('A' to 'Z').toList
val EXTRA_CHARS_LIST : List[Char] = List('.' , '_' , '>' , '<' , '=' , ';' , '\\', ':', ','); 
val DIGITS_NO_ZERO : Rexp = RANGE(('1' to '9').toList)

val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" 
val OP: Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||"
val LETTERS : Rexp = RANGE(LETTERS_LIST)
val SYMBOLS : Rexp = RANGE(LETTERS_LIST ::: EXTRA_CHARS_LIST ) 
val RPAREN: Rexp = "{" | "("
val LPAREN: Rexp = "}" | ")"
val SEMI: Rexp = ";"
val UNDERSCORE: Rexp = "_"
val WHITESPACE = PLUS(" " | "\n" | "\t" | "\r")
val NEWLINE = PLUS("\r\n" | "\r" | "\n")
val DIGIT = RANGE(('0' to '9').toList)



//Can recognise 0 but not numbers with leading 0s
val NUMBER = ((DIGIT) | (DIGITS_NO_ZERO ~ PLUS(DIGIT)))
val ID = LETTERS ~ (UNDERSCORE | LETTERS | DIGIT).% // star or PLUS
val STRING: Rexp = "\"" ~ (SYMBOLS | DIGIT | WHITESPACE).% ~ "\""
val COMMENT : Rexp = "//" ~ (SYMBOLS | CHAR(' ') | DIGIT).% ~ ONE


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) |
                  ("n" $ NUMBER) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("c" $ COMMENT) | 
                  ("w" $ WHITESPACE)).%


val token : PartialFunction[(String, String), Token] = {
  case ("s", _) => T_SEMI
  case ("p", "{") => T_LPAREN_C
  case ("p", "}") => T_RPAREN_C
  case ("p", "(") => T_LPAREN_N
  case ("p", ")") => T_RPAREN_N
  case ("i", s) => T_ID(s)
  case ("o", s) => T_OP(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("k", s) => T_KWD(s)
  case ("str", s) => T_STR(s)
}

def tokenise(s: String) : List[Token] = lexing_simp(WHILE_REGS, s).collect(token)

// Coursework 3 Code 

case class ~[+A, +B](x: A, y: B)

// constraint for the input
type IsSeq[A] = A => Seq[_]


abstract class Parser[I : IsSeq, T]{
    def parse(in: I): Set[(T, I)]
    def parse_all(in: I) : Set[T] = for ((hd, tl) <- parse(in); if tl.isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
    def parse(in: I) = 
        for ((hd1, tl1) <- p.parse(in); (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], q: => Parser[I, T]) extends Parser[I, T] {
    def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], f: T => S) extends Parser[I, S] {
    def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}



// Token Parser, checks for a token in the list
case class TokenParser(tkn : Token) extends Parser[List[Token], Token] {
  def parse(tkns : List[Token]) = tkns match {
    case head::rest => if (head == tkn) Set((head, rest)) else Set()
    case _ => Set()
  }
}

// more convenient syntax for parser combinators

implicit def token2TokenParser(t : Token) = TokenParser(t)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

implicit def TokenOps(s: Token) = new {
    def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](s, q)
    def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](s, q)
    def map[S] (f: => Token => S) = new MapParser[List[Token], Token, S](s, f)
//   def || (r: Token) = new AltParser[List[Token], Token](s, r)
//   def ==>[S] (f: => Token => S) = new MapParser[List[Token], Token, S](s, f)
//   def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](s, q)
//   def ~(r: Parser[List[Token], Token]) = new SeqParser[List[Token], Token, Token](s, r)
  
}



// atomic parser for (tokenised) strings
case class StrParserToken(tkn: String) extends Parser[String, String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_STR(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}

// StrParserToken.parse(List(T_STR("sing"), T_STR("song")))

// atomic parser for (tokenised) IDs
case object IdParserToken extends Parser[List[Token], String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_ID(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}

// IdParserToken.parse(List(T_ID("K88"),T_KWD("read")))


// atomic parser for numbers (transformed into ints)
case object NumParserToken extends Parser[List[Token], Int] {
  def parse(tkns: List[Token]) = tkns match {
    case T_NUM(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}

// NumParserToken.parse(List(T_NUM(88),T_KWD("read")))




// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp


// arithmetic expressions
lazy val AExp: Parser[List[Token], AExp] = 
    (Te ~ T_OP("+") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } || 
    (Te ~ T_OP("-") ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } ||
    Te

lazy val Te: Parser[List[Token], AExp] = 
    (Fa ~ T_OP("*") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
    (Fa ~ T_OP("/") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } || 
    (Fa ~ T_OP("%") ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } || 
    Fa  

lazy val Fa: Parser[List[Token], AExp] = 
    (T_LPAREN_N ~ AExp ~ T_RPAREN_N).map{ case _ ~ y ~ _ => y } || 
    IdParserToken.map(Var) || 
    NumParserToken.map(Num)

// Test 17 * (3+3)
AExp.parse_all(List(T_NUM(17), T_OP("*"), T_LPAREN_N, T_NUM(3), T_OP("+"), T_NUM(3), T_RPAREN_N))
// Test (121 % 2)
AExp.parse_all(List(T_LPAREN_N, T_NUM(121), T_OP("%"), T_NUM(2), T_RPAREN_N))

// boolean expressions with some simple nesting
lazy val BExp: Parser[String, BExp] = 
   (AExp ~ T_OP("==") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ T_OP("!=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ T_OP("<") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ T_OP(">") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ T_OP(">=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z)} ||
   (AExp ~ T_OP("<=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z)} ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("&&") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("||") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (T_KWD("true").map[BExp]{ _ => True }) || 
   (T_KWD("false").map[BExp]{ _ => False }) ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N).map[BExp]{ case _ ~ x ~ _ => x }

// Test (3>3) && (17!=18)
BExp.parse_all(List(T_LPAREN_N, T_NUM(3), T_OP(">"), T_NUM(3), T_RPAREN_N, T_OP("&&"), T_LPAREN_N, T_NUM(17), T_OP("!="), T_NUM(18), T_RPAREN_N))
// Test (3>3) || (17!=18)
BExp.parse_all(List(T_LPAREN_N, T_NUM(3), T_OP(">"), T_NUM(3), T_RPAREN_N, T_OP("||"), T_LPAREN_N, T_NUM(17), T_OP("!="), T_NUM(18), T_RPAREN_N))
// Test (3>3) || (17!=18) && (true)
BExp.parse_all(List(T_LPAREN_N, T_NUM(3), T_OP(">"), T_NUM(3), T_RPAREN_N, T_OP("||"), T_LPAREN_N, T_NUM(17), T_OP("!="), T_NUM(18), T_RPAREN_N, T_OP("&&"), T_LPAREN_N,  T_KWD("true"), T_RPAREN_N))
// Test (2<=17) || (200 >= 300)
BExp.parse_all(tokenise("(2<=17) || (200 >= 300)"))

// a single statement 
lazy val Stmt: Parser[String, Stmt] =
  ((p"skip".map[Stmt]{_ => Skip }) ||
   (IdParserToken ~ p":=" ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (p"write(" ~ IdParserToken ~ p")").map[Stmt]{ case _ ~ y ~ _ => Write(y) } ||
   (p"read" ~ IdParserToken) ==> { case _ ~ y => Read(y) } ||
   (p"if" ~ BExp ~ p"then" ~ Block ~ p"else" ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) })
 
 // Test skip
Stmt.parse_all(List(T_KWD("skip")))
// Test x := x + 1
Stmt.parse_all(List(T_ID("x"), T_OP(":="), T_ID("x"), T_OP("+"), T_NUM(1)))
// Test write x 
Stmt.parse_all(List(T_KWD("write"), T_ID("x")))
// Test write "muhahaha"
Stmt.parse_all(List(T_KWD("write"), T_STR("muhahaha")))
// Test write(x)
Stmt.parse_all(List(T_KWD("write"), T_LPAREN_N, T_ID("x"), T_RPAREN_N))
// Test write("muhahaha")
Stmt.parse_all(List(T_KWD("write"), T_LPAREN_N, T_STR("muhahaha"), T_RPAREN_N))
// Test read n
Stmt.parse_all(List(T_KWD("read"), T_ID("n")))
// Test if a == 3 then skip else a := a + 1 
Stmt.parse_all(List(T_KWD("if"), T_ID("a"), T_OP("=="), T_NUM(3), T_KWD("then"), T_KWD("skip"), T_KWD("else"), T_ID("a"), T_OP(":="), T_ID("a"), T_OP("+"), T_NUM(1)))
// Test if (a < b) then skip else a := a * b + 1
Stmt.parse_all(List(T_KWD("if"), T_LPAREN_N, T_ID("a"), T_OP("<"), T_ID("b"), T_RPAREN_N, T_KWD("then"), T_KWD("skip"), T_KWD("else"), T_ID("a"), T_OP(":="), T_ID("a"), T_OP("*"), T_ID("b"), T_OP("+"), T_NUM(1)))
// Test while a < 200 do a := a + 2
Stmt.parse_all(List(T_KWD("while"), T_ID("a"), T_OP("<"), T_NUM(200), T_KWD("do"), T_ID("a"), T_OP(":="), T_ID("a"), T_OP("+"), T_NUM(2))) 
// Test while (a < 20) do { x := x * 2; a := a + 1 }
Stmt.parse_all(List(T_KWD("while"), T_LPAREN_N, T_ID("a"), T_OP("<"), T_NUM(20), T_RPAREN_N, T_KWD("do"), T_LPAREN_N, T_ID("x"), T_OP(":="), T_ID("x"), T_OP("*"), T_NUM(2), T_SEMI, T_ID("a"), T_OP(":="), T_ID("a"), T_OP("+"), T_NUM(1), T_RPAREN_N))
// Test while (a >= 300) do { a := 300 - 16 - 20; b := 4 - b }
Stmt.parse_all(tokenise("while (a >= 300) do { a := 300 - 16 - 20; b := 4 - b }"))


// statements
lazy val Stmts: Parser[String, Block] =
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[String, Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))


// Examples
Stmt.parse_all("x2:=5+3")
Block.parse_all("{x:=5;y:=8}")
Block.parse_all("if(false)then{x:=5}else{x:=10}")


val fib = """n := 10;
             minus1 := 0;
             minus2 := 1;
             temp := 0;
             while (n > 0) do {
                 temp := minus2;
                 minus2 := minus1 + minus2;
                 minus1 := temp;
                 n := n - 1
             };
             result := minus2""".replaceAll("\\s+", "")

Stmts.parse_all(fib)


// an interpreter for the WHILE language
type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(i) => i
  case Var(s) => env(s)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)
}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case True => true
  case False => false
  case Bop("==", a1, a2) => eval_aexp(a1, env) == eval_aexp(a2, env)
  case Bop("!=", a1, a2) => !(eval_aexp(a1, env) == eval_aexp(a2, env))
  case Bop(">", a1, a2) => eval_aexp(a1, env) > eval_aexp(a2, env)
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case Bop(">=", a1, a2) => eval_aexp(a1, env) >= eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(x, a) => env + (x -> eval_aexp(a, env))
  case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env))
    else env
  case Write(x) => { println(env(x)) ; env }  
  case Read(x) => { // Dynamic read from console
    val input = scala.io.StdIn.readInt() 
    env + (x -> input)
  }
}


def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())

// parse + evaluate fib program; then lookup what is
// stored under the variable "result" 
println(eval(Stmts.parse_all(fib).head)("result"))



@arg(doc = "Tokens for fib and loops programs.")
@main
def main() = {
  println("Fib program")
}

