
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

define void @hanoi (i32 %n , i32 %a , i32 %b , i32 %c  ) {
   %tmp_0 = icmp ne i32  %n, 0
   br i1 %tmp_0, label %if_branch_3, label %else_branch_4

if_branch_3:
   %tmp_1 = sub i32  %n, 1
   call void @hanoi (i32 %tmp_1 , i32 %a , i32 %c , i32 %b  )
   call void @print_int (i32 %a)
   call void @print_char ([2 x i8] c"-\00")
   call void @print_char ([2 x i8] c">\00")
   call void @print_int (i32 %b)
   call void @print_char ([2 x i8] c"
\00")
   %tmp_2 = sub i32  %n, 1
   call void @hanoi (i32 %tmp_2 , i32 %c , i32 %b , i32 %a  )
   
   ret void

else_branch_4:
   call void @skip()
   ret void
}

define i32 @main() {
   call void @hanoi (i32 4 , i32 1 , i32 2 , i32 3  )
   ret i32 0
}

