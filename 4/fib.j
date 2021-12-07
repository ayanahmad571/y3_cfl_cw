
.class public fib.fib
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/print(I)V
    return 
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

.method public static read()I 
    .limit locals 10 
    .limit stack 10
    ldc 0 
    istore 1  ; this will hold our final integer 

; COMPILED CODE STARTS   

   invokestatic fib/fib/read()I
   istore 0 		; n
   ldc 0
   istore 1 		; minus1
   ldc 1
   istore 2 		; minus2
   ldc 0
   istore 3 		; temp
Loop_begin_0:
   ldc 0
   iload 0
   if_icmpge Loop_end_1
   iload 2
   istore 3 		; temp
   iload 1
   iload 2
   iadd
   istore 2 		; minus2
   iload 3
   istore 1 		; minus1
   iload 0
   ldc 1
   isub
   istore 0 		; n
   goto Loop_begin_0
Loop_end_1:
   iload 1 		; minus1
   invokestatic fib/fib/write(I)V

; COMPILED CODE ENDS
   return

.end method
