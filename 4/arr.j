
.class public arr.arr
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

; COMPILED CODE STARTS   

   ldc 10
   newarray int
   astore 0
   ldc 2
   newarray int
   astore 1
   aload 0
   ldc 0
   ldc 10
   iastore
   aload 0
   ldc 0
   iaload
   istore 2 		; x
   iload 2 		; x
   invokestatic arr/arr/write(I)V
   aload 1
   ldc 1
   ldc 5
   iastore
   aload 1
   ldc 1
   iaload
   istore 2 		; x
   iload 2 		; x
   invokestatic arr/arr/write(I)V

; COMPILED CODE ENDS
   return

.end method
