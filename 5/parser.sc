import scala.language.implicitConversions    
import scala.language.reflectiveCalls

import $file.tokeniser, tokeniser._ 

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

// atomic parser for numbers (transformed into ints)
case object DoubleParserToken extends Parser[List[Token], Double] {
  def parse(tkns: List[Token]) = tkns match {
    case T_FNUM(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}



abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String , args: List[(String , String)], ty: String , body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String , v: Int) extends Decl
case class FConst(name: String , x: Float) extends Decl
case class Call(name: String , args: List[Exp]) extends Exp
case class If(a: BExp , e1: Exp , e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp // integer numbers
case class FNum(i: Float) extends Exp // floating numbers
case class ChConst(c: Int) extends Exp // char constants
case class Aop(o: String , a1: Exp , a2: Exp) extends Exp
case class Sequence(e1: Exp , e2: Exp) extends Exp
case class Bop(o: String , a1: Exp , a2: Exp) extends BExp


// Grammar Rules for the Fun language

// arithmetic expressions
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Exp ~ T_KWD("else") ~ Exp) ==>
    { case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (M ~ T_SEMI ~ Exp) ==> { case x ~ _ ~ y => Sequence(x, y): Exp } || M

lazy val M: Parser[List[Token], Exp] =
  (T_KWD("write") ~ L) ==> { case _ ~ y => Write(y): Exp } || 
  (T_KWD("skip") ==> {_ => Skip }) ||
  (IdParserToken ~ T_OP(":=") ~ Exp) ==> { case x ~ _ ~ z => Assign(x, z) } ||
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Block ~ T_KWD("else") ~ Block) ==> { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
  (T_KWD("while") ~ BExp ~ T_KWD("do") ~ Block) ==> { case _ ~ y ~ _ ~ w => While(y, w) } ||
  (T_KWD("for") ~ Stmt ~ T_KWD("upto") ~ Exp ~ T_KWD("do") ~ Block) ==> { case _ ~ s ~ _ ~ a ~ _ ~ bl => For(s, a, bl): Stmt } ||


  (T_KWD("write") ~ T_LPAREN_N ~ IdParserToken ~ T_RPAREN_N_N) ==> { case _ ~ _ ~ y ~ _ => { WriteVar(y)} } ||
  (T_KWD("write") ~ StrParserToken) ==> { case _ ~ y => WriteStr(y) } ||
  (T_KWD("write") ~ IdParserToken) ==> { case _~ y => WriteVar(y)} ||
  (T_KWD("write") ~ T_LPAREN_N ~ StrParserToken ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => WriteStr(y) } ||

  (T_KWD("read") ~ IdParserToken) ==> { case _ ~ y => Read(y) } ||
  (T_KWD("read") ~ T_LPAREN_N ~ IdParserToken ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => Read(y) } ||

  (T_KWD("print_int") ~ T_LPAREN_N ~ NumParserToken ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
  (T_KWD("print_char") ~ T_LPAREN_N ~ StrParserToken ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
  (T_KWD("print_int") ~ T_LPAREN_N ~ F ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => WriteStr(y) } ||
  (T_KWD("print_char") ~ T_LPAREN_N ~ F ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => WriteStr(y) } ||


  || L

lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp) ==> { case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp) ==> { case x ~ _ ~ z => Aop("-", x, z): Exp } || T  

lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T) ==> { case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T) ==> { case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T) ==> { case x ~ _ ~ z => Aop("%", x, z): Exp } || F

lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_LPAREN_N ~ ListParser(Exp, T_COMMA) ~ T_RPAREN_N) ==> 
    { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (T_LPAREN_N ~ Exp ~ T_RPAREN_N) ==> { case _ ~ y ~ _ => y: Exp } || 
  IdParser ==> { case x => Var(x): Exp } || 
  NumParser ==> { case x => Num(x): Exp }

lazy val BExp: Parser[List[Token], BExp] = 
   (Exp ~ T_OP("==") ~ Exp) ==> { case x ~ _ ~ z => Bop("==", x, z) } || 
   (Exp ~ T_OP("!=") ~ Exp) ==> { case x ~ _ ~ z => Bop("!=", x, z) } || 
   (Exp ~ T_OP("<") ~ Exp) ==> { case x ~ _ ~ z => Bop("<", x, z) } || 
   (Exp ~ T_OP(">") ~ Exp) ==> { case x ~ _ ~ z => Bop("<", z, x) } ||
   (Exp ~ T_OP(">=") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", z, x)} ||
   (Exp ~ T_OP("<=") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", x, z)} ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("&&") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => And(y, v) } ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N ~ T_OP("||") ~ BExp) ==> { case _ ~ y ~ _ ~ _ ~ v => Or(y, v) } ||
   (T_KWD("true") ==> { _ => True }) || 
   (T_KWD("false") ==> { _ => False }) ||
   (T_LPAREN_N ~ BExp ~ T_RPAREN_N) ==> { case _ ~ x ~ _ => x }

lazy val Defn: Parser[List[Token], Decl] =
   (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ ListParser(IdParser, T_COMMA) ~ T_RPAREN_N ~ T_OP("=") ~ Exp) ==>
     { case _ ~ y ~ _ ~ w ~ _ ~ _ ~ r => Def(y, w, r): Decl }

lazy val Prog: Parser[List[Token], List[Decl]] =
  (Defn ~ T_SEMI ~ Prog) ==> { case x ~ _ ~ z => x :: z : List[Decl] } ||
  (Exp ==> ((s) => List(Main(s)) : List[Decl]))



// Reading tokens and Writing parse trees

import ammonite.ops._

def parse_tks(tks: List[Token]) : List[Decl] = 
  Prog.parse_single(tks)

//@doc("Parses a file.")
@main
def main(fname: String) : Unit = {
  val tks = tokenise(os.read(os.pwd / fname))
  println(tks)
  // println(parse_tks(tks))
}



