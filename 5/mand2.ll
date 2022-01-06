
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
   br i1 %tmp_0, label %if_branch_17, label %else_branch_18

if_branch_17:
   call void @print_char ([2 x i8] c" \00")
   
   ret void

else_branch_18:
   %tmp_4 = fmul double  %zi, %zi
   %tmp_5 = fmul double  %zr, %zr
   %tmp_3 = fadd double  %tmp_4, %tmp_5
   %tmp_2 = fcmp ole double  4.0, %tmp_3
   br i1 %tmp_2, label %if_branch_19, label %else_branch_20

if_branch_19:
   %tmp_7 = srem i32  %m, 10
   %tmp_8 = srem i32  %m, 10
   %tmp_6 = add i32  48, %tmp_8
   %p_c_21 = sub i32 %tmp_6, 48   
   call void @print_int_c(i32 %p_c_21)

   ret void

else_branch_20:
   %tmp_9 = add i32  %m, 1
   %tmp_12 = fmul double  %zr, %zr
   %tmp_13 = fmul double  %zi, %zi
   %tmp_11 = fsub double  %tmp_12, %tmp_13
   %tmp_10 = fadd double  %x, %tmp_11
   %tmp_16 = fmul double  %zr, %zi
   %tmp_15 = fmul double  2.0, %tmp_16
   %tmp_14 = fadd double  %tmp_15, %y
   call void @m_iter (i32 %tmp_9 , double %x , double %y , double %tmp_10 , double %tmp_14  )
   
   ret void
}

define void @x_iter (double %x , double %y  ) {
   %tmp_25 = load double , double* @Xmax
   %tmp_24 = fcmp ole double  %x, %tmp_25
   br i1 %tmp_24, label %if_branch_28, label %else_branch_29

if_branch_28:
   call void @m_iter (i32 0 , double %x , double %y , double 0.0 , double 0.0  )
   %tmp_27 = load double , double* @Xstep
   %tmp_26 = fadd double  %x, %tmp_27
   call void @x_iter (double %tmp_26 , double %y  )
   
   ret void

else_branch_29:
   call void @skip()
   ret void
}

define void @y_iter (double %y  ) {
   %tmp_31 = load double , double* @Ymax
   %tmp_30 = fcmp ole double  %y, %tmp_31
   br i1 %tmp_30, label %if_branch_35, label %else_branch_36

if_branch_35:
   %tmp_32 = load double , double* @Xmin
   call void @x_iter (double %tmp_32 , double %y  )
   call void @print_char ([2 x i8] c"
\00")
   %tmp_34 = load double , double* @Ystep
   %tmp_33 = fadd double  %y, %tmp_34
   call void @y_iter (double %tmp_33  )
   
   ret void

else_branch_36:
   call void @skip()
   ret void
}

define i32 @main() {
   %tmp_37 = load double , double* @Ymin
   call void @y_iter (double %tmp_37  )
   ret i32 0
}

