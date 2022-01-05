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


var fCol = List[(String, String)]()
var constCol = List[(String, String)]()
var varColTemp = List[(String, String)]()


def addNewFunction(name: String, ty: String) = {
  fCol = fCol ::: List((name, ty))
}

def addNewConst(name: String, ty: String) = {
  constCol = constCol ::: List((name, ty))
}

def addNewVar(name: String, ty: String) = {
  // println("Added temp var %", name, " with type: ", ty)
  varColTemp = varColTemp ::: List((name, ty))
}

def getItemType(name: String, colList: List[(String, String)]) : String = colList match {
  case x::xs => {
    if (x._1 == name) x._2
    else getItemType(name, xs)
  }
  case _ => "NA"
}



// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String) extends KVal 
// case class KVar(s: String, t: String) extends KVal

case object KSkip extends KVal
case object KEmpty extends KVal
case object KPrintSpace extends KVal
case object KPrintStar extends KVal
case object KNewLine extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(i: Float) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal], ty: String) extends KVal
case class KWrite(v: KVal) extends KVal
case class KWriteStr(s: String) extends KVal
case class KWriteInt(v: KVal) extends KVal
case class KWriteFloat(v: KVal) extends KVal
case class KWriteChar(s: Int) extends KVal
case class KWriteCharExp(s: KVal) extends KVal



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
case class KReturnV(v: KVal) extends KExp
case class KReturnF(v: KVal) extends KExp
case class KReturnD(v: KVal) extends KExp

def setLetDuo(y1: KVal, y2: KVal) : String = (y1,y2) match {
  case (KVar(a), KVar(b)) => {
    val aT = getItemType(a, varColTemp)
    val bT = getItemType(a, varColTemp)
    if (aT == "Int") bT
    else aT
  }
  case (KVar(a), KNum(b)) => getItemType(a, varColTemp)
  case (KNum(a), KVar(b)) => getItemType(b, varColTemp)
  case (KNum(a), KNum(b)) => "Int"
  case (KVar(a), KFNum(b)) => "Double"
  case (KFNum(a), KVar(b)) => "Double"
  case (KFNum(a), KFNum(b)) => "Double"
  case _ => { println ("Variable Match Error") ; sys.exit(-1) }
}



// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Skip => k(KSkip)
  case PrintSpace => KVoidPrint(KPrintSpace, k(KEmpty))
  case PrintStar => KVoidPrint(KPrintStar, k(KEmpty))
  case NewLine => KVoidPrint(KNewLine, k(KEmpty))
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
      CPS(e2)(y2 => {
        val iType = setLetDuo(y1, y2)
        addNewVar(z, iType)
        KLet(z, Kop(o, y1, y2), k(KVar(z)))
      }))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => {
        val iType = setLetDuo(y1, y2)
        addNewVar(z, iType)
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))
      }))
  }
  case Call(name, args) => {
    val getTy = getItemType(name, fCol)
    getTy match {
      case "Int" => {
        def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
          case Nil => {
              val z = Fresh("tmp")
              addNewVar(z, "Int")
              KLet(z, KCall(name, vs, "Int"), k(KVar(z)))
          }
          case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
        }
        aux(args, Nil)
      }
      case "Double" => {
        def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
          case Nil => {
              val z = Fresh("tmp")
              addNewVar(z, "Double")
              KLet(z, KCall(name, vs, "Double"), k(KVar(z)))
          }
          case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
        }
        aux(args, Nil)
      }
      case "Float" => {
        def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
          case Nil => {
              val z = Fresh("tmp")
              addNewVar(z, "Float")
              KLet(z, KCall(name, vs, "Float"), k(KVar(z)))
          }
          case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
        }
        aux(args, Nil)
      }
      case "Void" => {
        def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
          case Nil => {
              KVoidPrint(KCall(name, vs, "Void"), k(KEmpty))
          }
          case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
        }
        aux(args, Nil)
      }
    }
    
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))

  case PrintInt(e) => {
    CPS(e)(y => KVoidPrint(KWriteInt(y), k(KEmpty)))
  }
  case PrintFloat(e) => {
    CPS(e)(y => KVoidPrint(KWriteFloat(y), k(KEmpty)))
  }
  case PrintChar(e) => {
    val v = e.toInt
    KVoidPrint(KWriteChar(v), k(KEmpty))
  }
  case PrintCharExp(s, e) => {
    //Char, Id, Num
    val f = s.toInt
    val z = Fresh("tmp")
   
    CPS(e)(
      y => {
        CPS(Num(f))(y1 => 
          CPS(e)(y2 => {
            addNewVar(z, "Int")
            KLet(z, Kop("+", y1, y2), k(KWriteCharExp(KVar(z))))
          }))
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
def CPSv(e: Exp) = CPS(e)(KReturnV)
def CPSf(e: Exp) = CPS(e)(KReturnF)
def CPSd(e: Exp) = CPS(e)(KReturnD)


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
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
}

def paramsListToStrHelper(s: List[KVal]) : String = s match {
  case x :: xs => x match {
    case KVar(n) => {
      val iType = getItemType(n, varColTemp)
      if (iType == "NA" )
        k"i32 %${n} , " + paramsListToStrHelper(xs)
      else
        k"${retType(iType)} %${n} , " + paramsListToStrHelper(xs)
    }
    case KNum(n) => {
      k"i32 ${n} , " + paramsListToStrHelper(xs)
    }
    case KFNum(n) => {
      k"double ${n} , " + paramsListToStrHelper(xs)
    }
  }
  case Nil => ""
}

def paramsListToStr(s: List[KVal]) : String = {
  if (s.length < 1) ""
  else {
    val vals = paramsListToStrHelper(s);
    val p = vals.patch(vals.lastIndexOf(','), "", 1)
    p
  }
}

// compile K values
def compile_val(v: KVal) : String = v match {
  case KEmpty => ""
  case KNum(i) => s"$i"
  case KFNum(i) => s"$i"
  case KVar(s) => s"%$s"
  case Kop(op, x1, x2) => {
    val iType = setLetDuo(x1, x2)
    if (iType == "Int")
      s"${compile_op(op)} ${compile_val(x1)}, ${compile_val(x2)}"
    else
      s"${compile_dop(op)} ${compile_val(x1)}, ${compile_val(x2)}"
  }
  case KCall(x1, args, ty) => {
    s"call ${retType(ty)} @${x1} (${paramsListToStr(args)})"
  }
  case KWrite(x1) =>
    s"call void @print_int (i32 ${compile_val(x1)})"
  case KWriteInt(x1) => 
    {s"call void @print_int (i32 ${compile_val(x1)})"}
  case KWriteChar(n) =>
    s"call void @print_char ([2 x i8] c\"${(n).toChar}\\00\")"
  case KWriteCharExp(e) => {
    val z = Fresh("p_c")
    val z1 = Fresh("p_c")
    val z2 = Fresh("p_c")

    s"%${z} = sub i32 ${compile_val(e)}, 48" ++ 
    i"\n   call void @print_int_c(i32 %${z})"
  }
  case KSkip => "call void @skip()"
  case KNewLine => "call void @new_line()"
  case KPrintStar => "call void @print_star()"
  case KPrintSpace => "call void @print_space()"
}

// compile K expressions
def compile_exp(a: KExp) : String = a match {
  case KReturn(v) =>
    i"ret i32 ${compile_val(v)}"
  case KReturnV(v) => {
    i"${compile_val(v)}" ++
    i"ret void"
  }
  case KReturnF(v) =>
    i"ret double ${compile_val(v)}"
  case KReturnD(v) =>
    i"ret double ${compile_val(v)}"
  case KLet(x: String, v: KVal, e: KExp) => 
    i"%$x = ${compile_val(v)}" ++ compile_exp(e)
  case KIf(x, e1, e2) => {
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
    val iType = getItemType(e1, constCol)
    if (iType == "NA" )
      i"%${v} = load i32 , i32* @${e1}" ++ compile_exp(e2)
    else {
      addNewVar(v, iType)
      i"%${v} = load ${retType(iType)} , ${retType(iType)}* @${e1}" ++ compile_exp(e2)
    }
  }

}


val prelude = """
@.str = private constant [4 x i8] c"%d\0A\00"
@.str_n = private constant [3 x i8] c"%d\00"

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

define void @print_char([2 x i8] %0) {
  %k_1 = alloca [2 x i8]
  store [2 x i8] %0, [2 x i8]* %k_1
  %k_2 = bitcast [2 x i8]* %k_1 to [2 x i8]*
  %t0 = getelementptr [2 x i8], [2 x i8]* %k_2, i32 0, i32 0
  %2 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int_c(i32 %x) {
   %t0 = getelementptr [3 x i8], [3 x i8]* @.str_n, i32 0, i32 0
   call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
   ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)

"""
def retType(in: String) : String = in match {
  case "Int" => "i32"
  case "Double" => "double"
  case "Float" => "double"
  case "Void" => "void"

}

def argListToStringHelper(s: List[(String, String)]) : String = s match {
  case x :: xs => {
    addNewVar(x._1, x._2)
    k"${retType(x._2)} %${x._1} , " + argListToStringHelper(xs)
  }
  case Nil => ""
}

def argListToString(s: List[(String, String)]) : String = {
  varColTemp = List()
  if (s.length < 1) ""
  else {
    val vals = argListToStringHelper(s);
    val p = vals.patch(vals.lastIndexOf(','), "", 1)
    p
  }
}

// compile function for declarations and main
def compile_decl(d: Decl) : String = d match {
  case Def(name, args, ty, body) => {
    addNewFunction(name, ty)
    ty match {
      case "Int" => {
        m"define ${retType(ty)} @$name (${argListToString(args)}) {" ++
        compile_exp(CPSi(body)) ++
        m"}\n"
      }
      case "Double" => {
        m"define ${retType(ty)} @$name (${argListToString(args)}) {" ++
        compile_exp(CPSd(body)) ++
        m"}\n"
      }
      case "Float" => {
        m"define ${retType(ty)} @$name (${argListToString(args)}) {" ++
        compile_exp(CPSf(body)) ++
        m"}\n"
      }
      case "Void" => {
        m"define ${retType(ty)} @$name (${argListToString(args)}) {" ++
        compile_exp(CPSv(body)) ++
        m"}\n"
      }
    } 
    
  }
  case Main(body) => {
    // println(m"define i32 @main() {")
    m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0)))) ++
    m"}\n"
  }
  case Const(name, x) => {
    // println(m"@$name = global i32 $x \n")
    addNewConst(name, "Int")
    m"@$name = global i32 $x \n"
  }
  case FConst(name, x) => {
    addNewConst(name, "Float")
    m"@$name = global double $x \n"
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

