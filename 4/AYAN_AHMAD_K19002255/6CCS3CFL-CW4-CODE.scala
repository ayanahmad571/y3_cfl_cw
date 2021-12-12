/* 
 * Author: Ayan Ahmad
 * K-Number: K19002255
 * Email: ayan.ahmad@kcl.ac.uk
*/


// scalac test.scala
// javap -c Foo.class

// Copied Coursework 1, 2 and 3 code

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

val KEYWORD : Rexp = "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip" | "upto"
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
val COMMENT : Rexp = "//" ~ (SYMBOLS | CHAR(' ') | DIGIT).% ~ NEWLINE


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

implicit def tknParser(t : Token) = TokenParser(t)

implicit def ParserOps[I : IsSeq, T](p: Parser[I, T]) = new {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

implicit def TokenOps(p: Token) = new {
    def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](p, q)
    def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](p, q)
    def map[S] (f: => Token => S) = new MapParser[List[Token], Token, S](p, f)
}



// atomic parser for (tokenised) strings
case object StrParserToken extends Parser[List[Token], String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_STR(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}


// atomic parser for (tokenised) IDs
case object IdParserToken extends Parser[List[Token], String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_ID(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}



// atomic parser for numbers (transformed into ints)
case object NumParserToken extends Parser[List[Token], Int] {
  def parse(tkns: List[Token]) = tkns match {
    case T_NUM(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}



// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class For(s: Stmt, a : AExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Write(s: String) extends Stmt
case class Read(s: String) extends Stmt
case class WriteVar(s: String) extends Stmt
case class WriteStr(s: String) extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp
case class Lop(o: String , b1: BExp , b2: BExp) extends BExp


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


// boolean expressions with some simple nesting
lazy val BExp: Parser[List[Token], BExp] = 
   (AExp ~ T_OP("==") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ T_OP("!=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ T_OP("<") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ T_OP(">") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", z, x) } ||
   (AExp ~ T_OP(">=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", z, x)} ||
   (AExp ~ T_OP("<=") ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z)} ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("&&") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("||") ~ BExp).map[BExp]{ case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (T_KWD("true").map[BExp]{ _ => True }) || 
   (T_KWD("false").map[BExp]{ _ => False }) ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N).map[BExp]{ case _ ~ x ~ _ => x }

lazy val Stmt: Parser[List[Token], Stmt] =
  ((T_KWD("skip").map[Stmt]{_ => Skip }) ||
   (IdParserToken ~ T_OP(":=") ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (T_KWD("write") ~ T_LPAREN_N ~ IdParserToken ~ T_RPAREN_N).map[Stmt]{ case _ ~ _ ~ y ~ _ => { WriteVar(y)} } ||
   (T_KWD("write") ~ StrParserToken).map[Stmt]{ case _ ~ y => WriteStr(y) } ||
   (T_KWD("write") ~ IdParserToken).map[Stmt]{ case _~ y => WriteVar(y)} ||
   (T_KWD("write") ~ T_LPAREN_N ~ StrParserToken ~ T_RPAREN_N).map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
   (T_KWD("read") ~ IdParserToken).map[Stmt]{ case _ ~ y => Read(y) } ||
   (T_KWD("read") ~ T_LPAREN_N ~ IdParserToken ~ T_RPAREN_N).map[Stmt]{ case _ ~ _ ~ y ~ _ => Read(y) } ||
   (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Block ~ T_KWD("else") ~ Block)
   .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (T_KWD("while") ~ BExp ~ T_KWD("do") ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) } ||
   (T_KWD("for") ~ Stmt ~ T_KWD("upto") ~ AExp ~ T_KWD("do") ~ Block).map[Stmt]{ case _ ~ s ~ _ ~ a ~ _ ~ bl => For(s, a, bl): Stmt })
 

// statements
lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ T_SEMI ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((T_LPAREN_C ~ Stmts ~ T_RPAREN_C).map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))



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
  case Bop("<", a1, a2) => eval_aexp(a1, env) < eval_aexp(a2, env)
  case Bop("<=", a1, a2) => eval_aexp(a1, env) <= eval_aexp(a2, env)
  case And(b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Or(b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
    case Skip => env
    case Assign(x, a) => env + (x -> eval_aexp(a, env))
    case If(b, bl1, bl2) => if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env) 
    case While(b, bl) => if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env)) else env
    case WriteStr(x) => { 
      val un = StringContext treatEscapes x
      val r = un.replace("\"", "")
      print(r) ; env 
    }
    case WriteVar(x) => { print(env(x)) ; env }
    case Read(x) => {
        // Added for the sake of ease
        println("Waiting for User Input....")
        //https://stackoverflow.com/questions/5055349/how-to-take-input-from-a-user-in-scala/42968214
        val input = scala.io.StdIn.readInt() 
        env + (x -> input)
    }
}


def eval_bl(bl: Block, env: Env) : Env = bl match {
  case Nil => env
  case s::bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())

// for timing purposes - From PEP from Year 2
def time_needed[T](code: => T) = {

  val start = System.nanoTime()
  val finalRes =  code
  val end = System.nanoTime()
  println("Code Run Time: " + (end - start)/(1.0e9) + " s")
  finalRes
  println("________________")

}

// Coursework 3 Code

// additional statements for Arrays 
case class ArrayDef(s: String, n: Int) extends Stmt            // array definition
case class AssignA(s: String, a1: AExp, a2: AExp) extends Stmt // arr[exp1] := exp2
case class Ref(s: String, a: AExp) extends AExp


// compiler headers needed for the JVM
//
// - contains a main method and a method for writing out an integer
//
// - the stack and locals are hard-coded
//

val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/print(I)V
    return 
.end method

.method public static writes(Ljava/lang/String;)V
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return 
.end method

.method public static read()I 
    .limit locals 10 
    .limit stack 10
    ldc 0 
    istore 1  ; this will hold our final integer 
Label1: 
    getstatic java/lang/System/in Ljava/io/InputStream; 
    invokevirtual java/io/InputStream/read()I 
    istore 2 
    iload 2 
    ldc 13   ; the newline delimiter 
    isub 
    ifeq Label2 
    iload 2 
    ldc 32   ; the space delimiter 
    isub 
    ifeq Label2
    iload 2 
    ldc 48   ; we have our digit in ASCII, have to subtract it from 48 
    isub 
    ldc 10 
    iload 1 
    imul 
    iadd 
    istore 1 
    goto Label1 
Label2: 
    ;when we come here we have our integer computed in local variable 1 
    iload 1 
    ireturn 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS   

"""


val ending = """
; COMPILED CODE ENDS
   return

.end method
"""



// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// convenient string interpolations 
// for generating instructions and labels

implicit def sring_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}

def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
  case "/" => i"idiv"
  case "%" => i"irem"
}


// arithmetic expression compilation
def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)}"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
  case Ref(s, a) =>
    i"aload ${env(s)}" ++ compile_aexp(a, env) ++  i"iaload"
}

// boolean expression compilation
def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop("<=", a1, a2) =>
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case And(b1, b2) =>
    compile_bexp(b1, env, jmp) ++ compile_bexp(b2, env, jmp)
  case Or(b1, b2) =>
    val lfalse = Fresh("L_False")
    val stmt_tr = Fresh("End_Stmt_True") 
    compile_bexp(b1, env, lfalse) ++ i"goto $stmt_tr" ++ l"$lfalse" ++ compile_bexp(b2, env, jmp) ++ l"$stmt_tr"
     
}

// statement compilation
def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index)) 
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case For(st, ar, bl) => {
    // Here I and a equal to the values passed into st
    // ST here will be of the form Assign(x,y)
    // Hence i = x, and a = y
    val Assign(i, a) = st
    compile_block(
      List(
        st, 
        While(
          Bop("<=", Var(i), ar), 
          bl ++ List(Assign(i, Aop("+", Var(i), Num(1))))
        )
      ),
      env
    )
  }
  case Write(x) => 
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  case ArrayDef(s: String, n: Int) => {
    val index = if (env.isDefinedAt(s)) throw new Exception("array def error") else 
                    env.keys.size
    (i"ldc $n" ++
     i"newarray int" ++
     i"astore $index", env + (s -> index))
  }
  case AssignA(s, a1, a2) => {
    val index = if (env.isDefinedAt(s)) env(s) else 
                    throw new Exception("array not defined")
    (i"aload ${env(s)}" ++
     compile_aexp(a1, env) ++
     compile_aexp(a2, env) ++
     i"iastore", env)
  }
  case WriteVar(x) => 
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  case WriteStr(x) => 
    (i"ldc ${x} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)
  case Read(x) => {
    val index = env.getOrElse(x, env.keys.size) 
    (i"invokestatic XXX/XXX/read()I" ++ 
     i"istore $index \t\t; $x", env + (x -> index))
  }
}

// compile a block (i.e. list of statements)
def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}


// main compile function for blocks (adds headers and proper JVM names)
def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map())._1
  (beginning ++ instructions ++ ending).replace("XXX", class_name)
}


import ammonite.ops._

def compile_to_file(bl: Block, class_name: String) : Unit = 
  write.over(pwd / s"$class_name.j", compile(bl, class_name))  

def compile_and_run(bl: Block, class_name: String) : Unit = {
  println(s"Start of compilation")
  compile_to_file(bl, class_name)
  println(s"generated $class_name.j file")
  os.proc("java", "-jar", "jasmin.jar", s"$class_name.j").call()
  println(s"generated $class_name.class file ")
  //println(os.proc("java", s"${class_name}/${class_name}").call().out.text())
  // os.proc("java", s"${class_name}/${class_name}").call(stdout = os.Inherit)
  println("")
  println(s"You may now manually run the file.")
}



@arg(doc = "Question 1 Tests")
@main
def q1() = {
    val fib = """write "Fib: ";
    read n;
    minus1 := 1;
    minus2 := 0;
    while n > 0 do {
      temp := minus2;
      minus2 := minus1 + minus2;
      minus1 := temp;
      n := n - 1
    };
    write "Result: ";
    write minus2 ;
    write "\n""""

    val fact = """write "Fact: ";
    read n;
    x := 1;
    while n > 1 do {
        temp := x;
        x := temp * n;
        n := n - 1
    };
    write "Result";
    write x;
    write "\n""""


    // println(Stmts.parse_all(tokenise(fig1)).head)
    val fib_parsed = Stmts.parse_all(tokenise(fib)).head
    compile_and_run(fib_parsed, "fib")
    // println(Stmts.parse_all(tokenise(fact)))
    val fact_parsed = Stmts.parse_all(tokenise(fact)).head
    compile_and_run(fact_parsed, "fact")
}


@arg(doc = "Question 2 Tests")
@main
def q2() = {
    
    println("_____Q2 Tests______");

    val fig1 = """for i := 2 upto 4 do {
      write i;
      write "\n"
    }"""

    val fig_parsed = Stmts.parse_all(tokenise(fig1)).head
    compile_and_run(fig_parsed, "fors")


}


@arg(doc = "Question 3 Tests")
@main
def q3() = {

    println("_____Q3 Tests______");
    val fig1 = """for i := 1 upto 10 do {
      for i := 1 upto 10 do {
        write i;
        write "\n"
      }
    }"""

    val fig_parsed = Stmts.parse_all(tokenise(fig1)).head
    compile_and_run(fig_parsed, "nestedi")


}

@arg(doc = "All tests.")
@main
def all() = { 
    q1(); 
    q2(); 
    q3(); 
} 

