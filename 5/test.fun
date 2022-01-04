// a simple factorial program
// (including a tail recursive version)


def fact(n: Int) : Int =
  if n == 0 then 1 else n * fact(n - 1);

def facT(n: Int, acc: Int) : Int =
  if n == 0 then acc else facT(n - 1, n * acc);

def facTi(n: Int) : Int = facT(n, 1);

def top() : Void = {
  print_int(fact(6));
  print_char(',');
  print_int(facTi(6));
  print_char('\n')
};

top()

List(
  Def(
    fact,
    List((n,Int)),
    Int,
    If(
      Bop(==,Var(n),Num(0)),
      Num(1),
      Aop(*,Var(n),Call(fact,List(Aop(-,Var(n),Num(1)))))
    )
  ), 
  
  Def(
    facT,
    List((n,Int), (acc,Int)),
    Int,
    If(
      Bop(==,Var(n),Num(0)),
      Var(acc),
      Call(facT,List(Aop(-,Var(n),Num(1)), Aop(*,Var(n),Var(acc))))
    )
  ), 

  Def(
    facTi,
    List((n,Int)),
    Int,
    Call(facT,List(Var(n), Num(1)))
  ), 
  
  Def(
    top,
    List(),
    Void,
    Sequence(PrintInt(Call(fact,List(Num(6)))),Sequence(PrintChar(','),Sequence(PrintInt(Call(facTi,List(Num(6)))),PrintChar('\n'))))
  ), 
  
  Main(
    Call(top,List())
  )
)