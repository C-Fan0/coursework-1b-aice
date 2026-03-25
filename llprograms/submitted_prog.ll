define i64 @fib(i64 %n) {
  %1 = icmp slt i64 %n, 2
  br i1 %1, label %base, label %recurse
base:
  ret i64 %n
recurse:
  %2 = sub i64 %n, 1
  %3 = sub i64 %n, 2
  %4 = call i64 @fib(i64 %2)
  %5 = call i64 @fib(i64 %3)
  %6 = add i64 %4, %5
  ret i64 %6
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @fib(i64 10)
  ret i64 %1
}