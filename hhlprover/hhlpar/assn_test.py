"""Unit test for parallel assertions."""

import unittest

from hhlpar.assn_parser import parse_expr, parse_path_inv, parse_assn
from hhlpar.parallel import seq_hcsp_to_assn, add_pn_assn, sync_mult
from ss2hcsp.hcsp.parser import parse_hp_with_meta, parse_expr_with_meta
from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr
from wolframclient.language.expression import WLFunction, WLSymbol
from wolframclient.exception import WolframKernelException
from hhlpar.wolframengine_wrapper import solveODE, wl_prove, wl_reduce, wl_reduce_true, wl_reduce_false
from hhlpar.wolframengine_wrapper import wl_simplify, wl_polynomial_div, wl_is_polynomial, found_wolfram
from hhlpar.wolframengine_wrapper import session


class AssnTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            session.start()
        except Exception as e:
            session.start()

    @classmethod
    def tearDownClass(cls):
        session.terminate()

    def testParsePathInv(self):
        test_case = [
            "id_inv",
            "s == s0",
            "s == s0[x := v]",
        ]

        for s in test_case:
            path_inv = parse_path_inv(s)
            print(path_inv)

    def testParseAssn(self):
        test_case = [
            "init",

            # Example 1
            "wait_in(id_inv, ch1, {(d, v) =>"
            "  wait_outv(s == s0[x := v], ch2, v + 1, {d2 => init[x := v]})})",

            # Example 2
            # { P } *  ==  rec Q. skip || P; Q
            "rec Q. init || wait_in(id_inv, ch1, {(d, v) => Q[y := y + x][x := v]})",

            # Example 3
            "wait_in0(id_inv, ch2, {v =>"
            "  wait(s == s0[x := v], 1, {d1 =>"
            "    wait_outv(s == s0[x := v], ch1, v, {d2 => init[x := v]})})})",

            # Example 4
            "wait_outv(s == s0[x := 0], ch1, 1, {d1 =>"
            "  wait_in(s == s0[x := 2 * t], ch2, {(d2, v) =>"
            "    init[y := v][x := x + 2 * d2][x := 0]"
            "})}) ||"
            "wait_outv(s == s0[x := 0], ch1, 2, {d1 =>"
            "  wait_in(s == s0[x := t], ch2, {(d2, v) =>"
            "    init[y := v][x := x + d2][x := 0]"
            "})})",

            # Example 5
            "rec Q. init ||"
            "wait_outv(s == s0[x := 0], ch1, 1, {d1 =>"
            "  wait_in(s == s0[x := 2 * t], ch2, {(d2, v) =>"
            "    Q[y := v][x := x + 2 * d2][x := 0]"
            "})}) ||"
            "wait_outv(s == s0[x := 0], ch1, 2, {d1 =>"
            "  wait_in(s == s0[x := t], ch2, {(d2, v) =>"
            "    Q[y := v][x := x + d2][x := 0]"
            "})})"
        ]

        for s in test_case:
            assn = parse_assn(s)
            print(assn)

    def testSeqHcspToAssn(self):
        test_case = [
            # # Example 1
            # "ch1?x; ch2!(x+1);",

            # # Example 2
            # "{ ch1?x; y := y + x; }*",

            # # Example 3
            # "ch1!x; { ch1?x; y := y + x; }* ch1?x;",

            # # Example 4
            # "{ x := 0; { ch1?x; y := y + x; }* }*",

            # # Example 5
            # "wait (x); { ch1?x; y := y + x; }*",

            # # Example 6
            # "{x_dot=1 , y_dot=2 & x < 6 && y < 8} |> [] (ch1!x --> ch!y;) wait (5);",

            # # Example 7
            # "{x_dot=1 , y_dot=x & true} |> [] (ch1!x --> skip;, ch2?x --> skip;)",

            # # Example 8
            # "{x_dot=1 & x < 6} {x_dot=2 & x < 8}",

            # Example 9
            # "{x_dot=2 , y_dot=1 & y<8} wait (5);",

            # Example 101
            # "{ch1?x; }*",

            # Example 102
            # "{ch1!(x+1); }*" 

            "ch1?v;ch2?p;pp:=p+v*T+(1/2)*ad*T^2;vv:=v+da*T;if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (vv<=vl) {a:=da;} else {pp:=p+v*T; if ((op-pp)>=(vm^2)/(2*am)) { vl:=vm; } else if (op-pp>0) { vl:=(2*am*(op-pp))^1/2; } else { vl:=0; } if (v<=vl) {a:=0;} else {a:=-am;}} ch3!a;",

        ]
        F=[]
        for s in test_case:
            hp = parse_hp_with_meta(s)
            # print(hp)
            # print(seq_hcsp_to_assn(hp))
            print(add_pn_assn("A",seq_hcsp_to_assn(hp)))


    def testSyncAssn(self):
        test_case = [
            ("ch1?x;", {"chset":{"ch1"}}, "ch1!3;"),
            ("ch1?x; ch2?y;", {"chset":{"ch1"}}, "ch1!3;"),
            ("ch1?x; ch2!y;", {"chset":{"ch1"}}, "ch1!3;"),
            ("ch1?x; ch2!x;", {"chset":{"ch1"}}, "ch1!3;"),
            ("ch1!x; ch2?y;", {"chset":{"ch1", "ch2"}} , "ch1?z; ch2!(z+1);"),
            ("y:=0;{ch1!x; y:=y+1;}*", {"chset":{"ch1"}}, "y:=0;{ch1?x; y:=y+x;}*"),
            ("{ch1!x; y:=y+1;}*", {"chset":{"ch1"}, "init":"Ay==0&&By==0", "recinv":("AR1","BR1","By==Ay*Ax")}, "{ch1?x; y:=y+x;}*"),
            ("{x_dot=1 & true} |> [] (ch1!x --> skip;)", {"chset":{"ch1"}}, "{x_dot=1 & true} |> [] (ch1?y --> skip;)"),
            ("{x_dot=1 & true} |> [] (ch1!x --> skip;)", {"chset":{"ch1", "ch2"}}, "{x_dot=1 & true} |> [] (ch2?y --> skip;)"),
            ("{x_dot=1 & true} |> [] (ch1!x --> skip;)", {"chset":{}}, "{x_dot=1 & true} |> [] (ch2?y --> skip;)"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{"ch1"}, "init":"Ax==0"}, "wait (5); ch1!1;"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{}, "init":"Ax==Bx"}, "{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{"ch1", "ch2"}, "init":"Ax==Bx"}, "{x_dot=1 & x<8} |> [] (ch2?y --> skip;)"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{}}, "ch2?y;"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{"ch1", "ch2"}}, "ch2?y;"),
            ("{x_dot=1 & x<8} |> [] (ch1!x --> skip;)", {"chset":{"ch1"}}, "ch1?y;"),
            ("{x_dot=1 & x<8 +> ch1!x; } |> [] (ch1!x --> skip;)", {"chset":{"ch1"}, "init": "Ax==0"}, "wait (8); ch1?y;"),
            ("ch2?y;", {"chset":{}}, "{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"),
            ("ch2?y;", {"chset":{"ch1", "ch2"}}, "{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"),
            ("ch1?y;", {"chset":{"ch1"}}, "{x_dot=1 & x<8} |> [] (ch1!x --> skip;)"),
            ("x:=1;", {"chset":{"ch1"}}, "skip;"),
            ("{x_dot=1 , y_dot=2 & true} |> [] (ch1!x --> skip;)", {"chset":{"ch1"}}, "wait (1);ch1?x;"),
            ("wait (5);", {"chset":{"ch1"}}, "wait (2); wait (3);"),
            ("ch1?x;", {"chset":{"ch1"}}, "wait (y);ch1!3;"),
            ("ch1!x;", {"chset":{"ch1"}}, "wait (y);ch1?x;"),
            ("wait (y);ch1!x;", {"chset":{"ch1"}}, "ch1?x;"),
            (("ch2?x; wait (1);ch1!x;", {"chset":{"ch1"}}, "ch1?x;"), {"chset":{"ch2"}},"ch2!v;wait (1);"),
            ("x:=7;{x_dot=1 & x<6}", {"chset":{"ch1"}}, "skip;"),
            ("{x_dot=1 & x<6}", {"chset":{"ch1"}, "init": "Ax==7"}, "skip;"),
            ("{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *", {"chset":{"ch1", "ch2"}}, "{ch1?y; wait (y); ch2!0;}*"),
            ("{ x:=0; {ch1!2; {x_dot=1 & true} |> [] (ch2?y --> skip;)} ++ {ch1!1; {x_dot=2 & true} |> [] (ch2?y --> skip;)} } *", {"chset":{"ch1", "ch2"}, "init": "Ax==0", "recinv":("AR1","BR1","Ax>=0&&Ax<=2")}, "{ch1?y; wait (y); ch2!0;}*"),
            (("{{x_dot=1 & true} |> [] (ch3?x --> ch1!0;,ch2?x --> skip;)}*",{"chset":{"ch1", "ch2"}},"{{x_dot=1 & true} |> [] (ch4?x --> ch2!0;,ch1?x --> skip;)}*"),{"chset":{"ch3", "ch4"}},"{wait (5);{ch3!0;} ++ {ch4!0;}}*"),
            ("ch1!v;ch2!p; {ch3?a; {p_dot=v, v_dot=a & true} |> [] (ch1!v --> ch2!p;) }*", 
             {"chset":{"ch1", "ch2", "ch3"}, 
              "init": """BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                        ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                        (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))""" , 
              "recinv": ("AR1","BR1","""BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&
                         ((((2*Bam)*(Bop-Ap)>=(Bvm^2))&&(Av<=Bvm))||
                         (((2*Bam)*(Bop-Ap)<(Bvm^2))&&(Av<=0||Av^2<=(2*Bam*(Bop-Ap)))))
                         &&Av==Bv&&Ap==Bp""")},
             """ch1?v;ch2?p;
             {pp:=p+v*T+(1/2)*da*T^2;vv:=v+da*T;
             if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
             else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
             else { vlm:=0; } 
             if (vv<=0||vv^2<=vlm) {a:=da;} 
             else {pp:=p+v*T; 
                if ((2*am)*(op-pp)>=(vm^2)) { vlm:=vm^2; } 
                else if (op-pp>0) { vlm:=(2*am*(op-pp)); } 
                else { vlm:=0; } 
                if (v<=0||v^2<=vlm) {a:=0;} 
                else {a:=-am;}} 
            ch3!a;wait (T); ch1?v;ch2?p;}*""")
        ]
        for s in test_case:
            print(sync_mult(s))
        

    def testexpr(self):
        test_case = [
            # "x<=y||x==1",
            "x==2->x>0",
            # "Ax>0||Bx<=0",
            # "d1==6-2*x&&d1<5-2*x",
            # "exists x1 . (x==x1+1 && x1>0)",
            "(if x>0 then x else -x)>=0",
            # "(if (Bop-Ap>=(Bvm^2)/(2*Bam)) then (Av<=Bvm) else (Av<=(2*Bam*(Bop-Ap))^1/2))",
            # "if (Av+Bda*BT<=(if (Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)>=(Bvm^2)/(2*Bam)) then (Bvm) else (if (Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)>0) then ((2*Bam*(Bop-(Ap+Av*BT+(1/2)*Bda*BT^2)))^1/2) else (0)))) then (Aa==Bda) else (if (Av<=(if (Bop-(Ap+Av*BT)>=(Bvm^2)/(2*Bam)) then (Bvm) else (if (Bop-(Ap+Av*BT)>0) then ((2*Bam*(Bop-(Ap+Av*BT)))^1/2) else (0)))) then (Aa==0) else (Aa==-Bam))",
            # "BT>0&&Bam>0&&Bda>0&&Bvm>0&&Ap<=Bop&&(if (Bop-Ap>=(Bvm^2)/(2*Bam)) then (Av<=Bvm) else (if (Bop-Ap>0) then (Av<=(2*Bam*(Bop-Ap))^1/2) else (Av<=0)))"
        ]
        for s in test_case:
            print(parse_expr_with_meta(s))
            # print(wl_reduce(parse_expr_with_meta(s),[]))
            # print(wl_prove(parse_expr_with_meta(s),[]))
            # print(wl_reduce_false(parse_expr_with_meta(s)))


if __name__ == "__main__":
    unittest.main()
