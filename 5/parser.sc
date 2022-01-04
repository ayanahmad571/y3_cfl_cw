import scala.language.implicitConversions    
import scala.language.reflectiveCalls

import $file.tokeniser, tokeniser._ 


// Parser combinators
//    type parameter I needs to be of Seq-type
//
abstract class Parser[I, T](implicit ev: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(_._2.isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { println ("Parse Error") ; sys.exit(-1) }
    }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

class SeqParser[I, T, S](p: => Parser[I, T], 
                         q: => Parser[I, S])(implicit ev: I => Seq[_]) extends Parser[I, ~[T, S]] {
  def parse(sb: I) = 
    for ((head1, tail1) <- p.parse(sb); 
         (head2, tail2) <- q.parse(tail1)) yield (new ~(head1, head2), tail2)
}

class AltParser[I, T](p: => Parser[I, T], 
                      q: => Parser[I, T])(implicit ev: I => Seq[_]) extends Parser[I, T] {
  def parse(sb: I) = p.parse(sb) ++ q.parse(sb)   
}

class FunParser[I, T, S](p: => Parser[I, T], 
                         f: T => S)(implicit ev: I => Seq[_]) extends Parser[I, S] {
  def parse(sb: I) = 
    for ((head, tail) <- p.parse(sb)) yield (f(head), tail)
}

// convenient combinators
implicit def ParserOps[I, T](p: Parser[I, T])(implicit ev: I => Seq[_]) = new {
  def || (q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ==>[S] (f: => T => S) = new FunParser[I, T, S](p, f)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
}

def ListParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)) ==> { case x ~ _ ~ z => x :: z : List[T] } ||
  (p ==> ((s) => List(s)))
}

def ArgParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[(T, String)]] = {
  // println(p, q)
  (p ~ q ~ ArgParser(p, q)) ==> { case x ~ _ ~ z => (x, "Int") :: z : List[(T, String)] } ||
  (p ==> (s => List((s, "Int")))) 
  // () ==> {case _ => List()}
}

// ArgTypeParser(IdParser, T_COMMA)

def ArgTypeParser[I, T, S, K, N](p: => Parser[I, T], q: => Parser[I, S], r: => Parser[I, K], t: => Parser[I, N])(implicit ev: I => Seq[_]): Parser[I, List[(T, K)]] = {
  // println(p, q ,r, t)
  (p ~ q ~ r ~ t ~ ArgTypeParser(p, q, r, t)) ==> { case x ~ _ ~ z ~ _ ~ y => (x,z) :: y : List[(T, K)] } ||
  (p ~ q ~ r ) ==> {case x ~ _ ~ z => List((x, z))} 
  // () ==> {case _ => List()}
}

// ArgTypeParser( p-> IdParser, q-> T_OP(":"), r-> TypeParser, t-> T_COMMA)


case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) = TokParser(t)

implicit def TokOps(t: Token) = new {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def ==>[S] (f: => Token => S) = new FunParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_NUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}

case object FloatParser extends Parser[List[Token], Float] {
  def parse(ts: List[Token]) = ts match {
    case T_FNUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}
case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object IdConstParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID_CONST(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

// atomic parser for (tokenised) strings
case object StrParserToken extends Parser[List[Token], String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_STR(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}

// atomic parser for (tokenised) strings
case object TypeParser extends Parser[List[Token], String] {
  def parse(tkns: List[Token]) = tkns match {
    case T_TYPE(tk)::rest => Set((tk, rest))
    case _ => Set()
  }
}


// Abstract syntax trees for the Fun language
abstract class Exp extends Serializable 
abstract class BExp extends Serializable 
abstract class Decl extends Serializable 


case class Def(name: String , args: List[(String , String)], ty: String , body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String , v: Int) extends Decl
case class FConst(name: String , x: Float) extends Decl


case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Write(e: Exp) extends Exp


case class WriteStr(e: String) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp // integer numbers
case class FNum(i: Float) extends Exp // floating numbers
case class ChConst(c: String) extends Exp // char constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp

case object Skip extends Exp
case class PrintInt(e: Exp) extends Exp
case class PrintFloat(e: Exp) extends Exp
case object PrintSpace extends Exp
case object PrintStar extends Exp
case class PrintChar(e: String) extends Exp
case class PrintCharExp(s: String, e: Exp) extends Exp
case object NewLine extends Exp

case class Bop(o: String, a1: Exp, a2: Exp) extends BExp



// Grammar Rules for the Fun language

// arithmetic expressions
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Exp ~ T_KWD("else") ~ Exp) ==> { case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C ~ T_KWD("else") ~ Exp) ==> { case _ ~ x ~ _ ~ _ ~ y ~ _ ~ _ ~ z => If(x, y, z): Exp } ||
  (T_KWD("if") ~ BExp ~ T_KWD("then")  ~ Exp  ~ T_KWD("else") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C) ==> { case _ ~ x ~ _ ~ y ~  _ ~ _ ~ z ~ _=> If(x, y, z): Exp } ||
  (M ~ T_SEMI ~ Exp) ==> { case x ~ _ ~ y => Sequence(x, y): Exp } || M

lazy val M: Parser[List[Token], Exp] =
  (T_KWD("skip")) ==> {case _ => Skip : Exp } ||
  (T_KWD("skip") ~ T_LPAREN_N ~ T_RPAREN_N) ==> {case _ ~ _ ~ _ => Skip : Exp } ||
  (T_KWD("write") ~ L) ==> { case _ ~ y => Write(y): Exp } ||
  (T_KWD("write") ~ StrParserToken) ==> { case _ ~ y => WriteStr(y): Exp } || 
  (T_KWD("new_line") ~ T_LPAREN_N ~ T_RPAREN_N ) ==> { case _ ~ _ ~  _ => NewLine: Exp } || 
  (T_KWD("print_star") ~ T_LPAREN_N ~ T_RPAREN_N ) ==> { case _ ~ _ ~  _ => PrintStar: Exp } || 
  (T_KWD("print_space") ~ T_LPAREN_N ~ T_RPAREN_N ) ==> { case _ ~ _ ~  _ => PrintSpace: Exp } || 
  (T_KWD("print_int") ~ T_LPAREN_N ~ Exp ~ T_RPAREN_N ) ==> { case _ ~ _ ~ y ~ _ => PrintInt(y): Exp } || 
  // (T_KWD("print_int") ~ T_LPAREN_N ~ NumParser ~ T_RPAREN_N ) ==> { case _ ~ _ ~ y ~ _ => PrintInt(): Exp } || 
  (T_KWD("print_char") ~ T_LPAREN_N ~ StrParserToken ~ T_RPAREN_N) ==> { case _ ~ _ ~ y ~ _ => PrintChar(y): Exp } ||
  (T_KWD("print_char") ~ T_LPAREN_N ~ StrParserToken ~ T_OP("+") ~ T_LPAREN_N ~ Exp ~ T_RPAREN_N ~ T_RPAREN_N) ==> 
    { case _ ~ _ ~ y ~ _ ~ _ ~ w ~ _ ~ _  => {PrintCharExp(y,w): Exp} } || L


lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp) ==> { case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp) ==> { case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] = 
  (F ~ T_OP("*") ~ T) ==> { case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T) ==> { case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T) ==> { case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_LPAREN_N ~ ListParser(Exp, T_COMMA) ~ T_RPAREN_N) ==> { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (IdParser ~ T_LPAREN_N ~ T_RPAREN_N) ==> { case x ~ _ ~ _ => Call(x, List()): Exp } ||
  (T_LPAREN_N ~ Exp ~ T_RPAREN_N) ==> { case _ ~ y ~ _ => y: Exp } || 
  IdParser ==> { case x => Var(x): Exp } || 
  IdConstParser ==> { case x => Var(x): Exp } || 
  NumParser ==> { case x => Num(x): Exp } ||
  FloatParser ==> { case x => FNum(x): Exp }


// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp) ==> { case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp) ==> { case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp)  ==> { case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP("=>") ~ Exp) ==> { case x ~ _ ~ z => Bop("<=", z, x): BExp }  

lazy val Defn: Parser[List[Token], Decl] =
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ ArgParser(IdParser, T_COMMA) ~ T_RPAREN_N ~ T_OP("=") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C ) ==>
     { case _ ~ y ~ _ ~ w ~ _ ~ _ ~ _ ~ r ~ _ => Def(y, w, "Int",  r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ ArgTypeParser(IdParser, T_OP(":"), TypeParser, T_COMMA) ~ T_RPAREN_N ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C) ==>
     { case _ ~ y ~ _ ~ w ~ _ ~ _ ~ t ~ _ ~ _ ~ r ~ _ => Def(y, w, t, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ ArgParser(IdParser, T_COMMA) ~ T_RPAREN_N ~ T_OP("=") ~ Exp) ==>
     { case _ ~ y ~ _ ~ w ~ _ ~ _ ~ r => Def(y, w, "Int",  r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ ArgTypeParser(IdParser, T_OP(":"), TypeParser, T_COMMA) ~ T_RPAREN_N ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ Exp) ==>
     { case _ ~ y ~ _ ~ w ~ _ ~ _ ~ t ~ _ ~ r => Def(y, w, t,  r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ T_RPAREN_N ~ T_OP("=") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C ) ==>
     { case _ ~ y ~ _ ~ _ ~ _ ~ _ ~ r ~ _ => Def(y, List(), "Int",  r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ T_RPAREN_N ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ T_LPAREN_C ~ Exp ~ T_RPAREN_C) ==>
     { case _ ~ y ~ _ ~ _ ~ _ ~ t ~ _ ~ _ ~ r ~ _ => Def(y, List(), t, r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ T_RPAREN_N ~ T_OP("=") ~ Exp) ==>
     { case _ ~ y ~ _ ~ _ ~ _ ~ r => Def(y, List(), "Int",  r): Decl } ||
  (T_KWD("def") ~ IdParser ~ T_LPAREN_N ~ T_RPAREN_N ~ T_OP(":") ~ TypeParser ~ T_OP("=") ~ Exp) ==>
     { case _ ~ y ~ _ ~ _ ~ _ ~ t ~ _ ~ r => Def(y, List(), t,  r): Decl } 
  
lazy val Consts: Parser[List[Token], Decl] =
  (T_KWD("val") ~ IdConstParser ~ T_OP(":") ~ T_TYPE("Int") ~ T_OP("=") ~ NumParser ) ==> { case _ ~ y ~ _ ~ _ ~ _ ~ r => Const(y, r): Decl } ||
  (T_KWD("val") ~ IdConstParser ~ T_OP(":") ~ T_TYPE("Float") ~ T_OP("=") ~ FloatParser ) ==> { case _ ~ y ~ _ ~ _ ~ _ ~ r => FConst(y, r): Decl } ||
  (T_KWD("val") ~ IdConstParser ~ T_OP(":") ~ T_TYPE("Double") ~ T_OP("=") ~ FloatParser ) ==> { case _ ~ y ~ _ ~ _ ~ _ ~ r => FConst(y, r): Decl }   


lazy val Prog: Parser[List[Token], List[Decl]] =
  (Consts ~ T_SEMI ~ Prog) ==> { case x ~ _ ~ z => x :: z : List[Decl] } ||
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
  println(parse_tks(tks))
}


