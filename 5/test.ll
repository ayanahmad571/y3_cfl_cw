
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

define void @print_char([2 x i8] %0) {
  %k_1 = alloca [2 x i8]
  store [2 x i8] %0, [2 x i8]* %k_1
  %k_2 = bitcast [2 x i8]* %k_1 to [2 x i8]*
  %t0 = getelementptr [2 x i8], [2 x i8]* %k_2, i32 0, i32 0
  %2 = call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

; END OF BUILD-IN FUNCTIONS (prelude)

@Ymin = global double -1.3 

@Ymax = global double 1.3 

@Ystep = global double 0.05 

@Xmin = global double -2.1 

@Xmax = global double 1.1 

@Xstep = global double 0.02 

@Maxiters = global i32 1000 

define void @m_iter (i32 %m , double %x , double %y , double %zr , double %zi  ) {
   %tmp_1 = load i32 , i32* @Maxiters
   %tmp_0 = icmp sle i32  %tmp_1, %m
   br i1 %tmp_0, label %if_branch_14, label %else_branch_15

if_branch_14:
   call void @print_star()
   
   ret void

else_branch_15:
   %tmp_4 = mul i32  %zi, %zi
   %tmp_5 = mul i32  %zr, %zr
   %tmp_3 = add i32  %tmp_4, %tmp_5
   %tmp_2 = icmp sle i32  4.0, %tmp_3
   br i1 %tmp_2, label %if_branch_16, label %else_branch_17

if_branch_16:
   call void @print_space()
   
   ret void

else_branch_17:
   %tmp_6 = add i32  %m, 1
   %tmp_9 = mul i32  %zr, %zr
   %tmp_10 = mul i32  %zi, %zi
   %tmp_8 = sub i32  %tmp_9, %tmp_10
   %tmp_7 = add i32  %x, %tmp_8
   %tmp_13 = mul i32  %zr, %zi
   %tmp_12 = mul i32  2.0, %tmp_13
   %tmp_11 = add i32  %tmp_12, %y
   call void @m_iter (i32 %tmp_6 , double %x , double %y , i32 %tmp_7 , i32 %tmp_11  )
   
   ret void
}

define void @x_iter (double %x , double %y  ) {
   %tmp_19 = load double , double* @Xmax
   %tmp_18 = icmp sle i32  %x, %tmp_19
   br i1 %tmp_18, label %if_branch_22, label %else_branch_23

if_branch_22:
   call void @m_iter (i32 0 , double %x , double %y , double 0.0 , double 0.0  )
   %tmp_21 = load double , double* @Xstep
   %tmp_20 = add i32  %x, %tmp_21
   call void @x_iter (i32 %tmp_20 , double %y  )
   
   ret void

else_branch_23:
   call void @skip()
   ret void
}

define void @y_iter (double %y  ) {
   %tmp_25 = load double , double* @Ymax
   %tmp_24 = icmp sle i32  %y, %tmp_25
   br i1 %tmp_24, label %if_branch_29, label %else_branch_30

if_branch_29:
   %tmp_26 = load double , double* @Xmin
   call void @x_iter (i32 %tmp_26 , double %y  )
   call void @new_line()
   %tmp_28 = load double , double* @Ystep
   %tmp_27 = add i32  %y, %tmp_28
   call void @y_iter (i32 %tmp_27  )
   
   ret void

else_branch_30:
   call void @skip()
   ret void
}

define i32 @main() {
   %tmp_31 = load double , double* @Ymin
   call void @y_iter (i32 %tmp_31  )
   ret i32 0
}

