/* 
 * Author: Ayan Ahmad
 * K-Number: K19002255
 * Email: ayan.ahmad@kcl.ac.uk
*/

// Copied Coursework 1, 2, 3 and 4 code



import $file.tokeniser, tokeniser._
import $file.parser, parser._ 

import scala.language.implicitConversions    
import scala.language.reflectiveCalls 


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String) extends KVal
case class KVarC(s: String) extends KVal
// case class KVar(s: String, ty: Ty = "UNDEF") extends KVal

case object KSkip extends KVal
case object KPrintSpace extends KVal
case object KPrintStar extends KVal
case object KNewLine extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(i: Float) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal]) extends KVal
case class KWrite(v: KVal) extends KVal
case class KWriteStr(s: String) extends KVal
case class KWriteInt(v: KVal) extends KVal
case class KWriteFloat(v: KVal) extends KVal
case class KWriteChar(s: Int) extends KVal



case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}

case class KVoidPrint(e1: KVal, e2: KExp) extends KExp
case class KConstVar(v: String, e1: String, e2: KExp) extends KExp


case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal) extends KExp

// def typ_val(v: KVal , ts: TyEnv) = ???
// def typ_exp(a: KExp , ts: TyEnv) = ???

// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Skip => k(KSkip)
  case PrintSpace => k(KPrintSpace)
  case PrintStar => k(KPrintStar)
  case NewLine => KVoidPrint(KNewLine, k(KNewLine))
  case Var(s) => k(KVar(s))
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case WriteStr(e) => k(KWriteStr(e))
  case VarC(s) => {
    val z = Fresh("tmp")
    KConstVar(z, s, k(KVar(z)))
  }
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))

  case PrintInt(e) => {
    // val z = Fresh("tmp")
    // CPS(e)(y => KLet(z, KWriteInt(y), k(KVar(z))))
    CPS(e)(y => KVoidPrint(KWriteInt(y), k(KWriteInt(y))))
  }
  case PrintFloat(e) => CPS(e)(y => k(KWriteFloat(y)))
  case PrintChar(e) => {
    val z = Fresh("tmp")
    val v = e.toInt
    KLet(z, KWriteChar(v), k(KVar(z)))
  }
  case PrintCharExp(s, e) => {
    val f = s.toInt
    val z = Fresh("tmp")
    CPS(e)(
      y => {
        CPS(Num(f))(y1 => 
          CPS(e)(y2 => KLet(z, Kop("+", y1, y2), k(KVar(z)))))
      }
    )
  }
  case Write(e) => {
    val z = Fresh("tmp")
    CPS(e)(y => KLet(z, KWrite(y), k(KVar(z))))
  }
}   

//Const
//FConst
//ChConst

//initial continuation
def CPSi(e: Exp) = CPS(e)(KReturn)

// val ai = List(("m", "Int"),("m", "Int"),("m", "Int"),("m", "Int"))

// println(argListToString(ai))

// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def string_inters(sc: StringContext) = new {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
    def k(args: Any*): String = sc.s(args:_*)
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 "     // signed less than
}

def compile_dop(op: String) = op match {
  case "+" => "fadd float "
  case "*" => "fmul float "
  case "-" => "fsub float "
  case "==" => "fcmp oeq float "
  case "!=" => "fcmp one float "
  case "<=" => "fcmp ole float "
  case "<" => "fcmp olt float "
}

// compile K values
def compile_val(v: KVal) : String = v match {
  case KNum(i) => s"$i"
  case KVar(s) => s"%$s"
  case KVar(s) => s"%$s"
  case Kop(op, x1, x2) => 
    s"${compile_op(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  case KCall(x1, args) => 
    s"call i32 @$x1 (${args.map(compile_val).mkString("i32 ", ", i32 ", "")})"
  case KWrite(x1) =>
    s"call void @print_int (i32 ${compile_val(x1)})"
  case KWriteInt(x1) => 
   {println("ssssss"); s"call void @print_int (i32 ${compile_val(x1)})"}
  case KSkip => "call void @skip()"
  case KNewLine => "call void @new_line()"
}

// compile K expressions
def compile_exp(a: KExp) : String = a match {
  case KReturn(v) =>
    // println("_____Ret_____")
    // println(v)
    i"ret i32 ${compile_val(v)}"
  case KLet(x: String, v: KVal, e: KExp) => 
    i"%$x = ${compile_val(v)}" ++ compile_exp(e)
  case KIf(x, e1, e2) => {
    // println("_____If_____")
    // println(e1)
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1) ++
    l"\n$else_br" ++ 
    compile_exp(e2)
  }
  case KVoidPrint(e1, e2) => {
    i"${compile_val(e1)}" ++ compile_exp(e2)
  }
  case KConstVar(v, e1, e2) => {
    i"%${v} = load i32 , i32* @${e1}" ++ compile_exp(e2)
  }

}


val prelude = """
@.str = private constant [4 x i8] c"%d\0A\00"

declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  %1 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @skip() #0 {
  ret void
}

define void @print_int(i32 %x) {
   %t0 = getelementptr [4 x i8], [4 x i8]* @.str, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)

"""
def retType(in: String) : String = in match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Float" => "float"
  case "Void" => "void"

}

def argListToStringHelper(s: List[(String, String)]) : String = s match {
  case x :: xs => k"${retType(x._2)} %${x._1} , " + argListToStringHelper(xs)
  case Nil => ""
}

def argListToString(s: List[(String, String)]) : String = {
  val vals = argListToStringHelper(s);
  val p = vals.patch(vals.lastIndexOf(','), "", 1)
  p
}

// compile function for declarations and main
def compile_decl(d: Decl) : String = d match {
  case Def(name, args, ty, body) => { 
    // println(m"define ${retType(ty)} @$name (${argListToString(args)}) {")
    m"define ${retType(ty)} @$name (${argListToString(args)}) {" ++
    compile_exp(CPSi(body)) ++
    m"}\n"

  }
  case Main(body) => {
    // println(m"define i32 @main() {")
    m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0)))) ++
    m"}\n"
    

  }
  case Const(name, x) => {
    // println(m"@$name = global i32 $x \n")
    m"@$name = global i32 $x \n"
  }
  case FConst(name, x) => {
    m"@$name = global float $x \n"
  }
}


// main compiler functions
def compile(prog: List[Decl]) : String = 
  prelude ++ (prog.map(compile_decl).mkString)


import ammonite.ops._


@main
def main(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    println("Tokenise___________________")
    println(tks)
    println("_____________________________________")
    
    val ast = parse_tks(tks)
    println("Parse___________________")
    println(ast)
    println("_________________________________________")
 
    println("Compile___________________")
    println(compile(ast))
    println("_________________________________________")
}

@main
def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = parse_tks(tks)
    val code = compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}


// https://groups.google.com/g/llvm-dev/c/1QWIjlrd8O8
// Code here had to be changed for my machine
// Else it was throwing this error:
// R_X86_64_32 against `.rodata' can not be used when making a PIE object
@main
def run(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    write(fname)  
    os.proc("llc", "-filetype=obj", "--relocation-model=pic", file ++ ".ll").call()
    os.proc("gcc", "-fPIE",  file ++ ".o", "-o", file ++ ".bin").call()
    os.proc(os.pwd / (file ++ ".bin")).call(stdout = os.Inherit)
    println(s"done.")
}


