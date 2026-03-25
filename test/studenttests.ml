open Util.Assert
open Gradedtests
    

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  GradedTest("Posted Test Case", 5, [
    ("posted_test", assert_eqf (fun () -> exec_e2e_file "llprograms/submitted_prog.ll" "") 55L)
  ])
]