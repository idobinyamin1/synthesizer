
def test1():

    # feature2

    # basic test
    input = "y := ?? ; assert y == 10;"
    output = "y := 10 ;"

    # simple arithmetic
    input = "x := 5 ; y := x + ?? ; assert y == 10;"
    output = "x := 5 ; y := x + 5"


    # simple arithmetic with dependency between variables in the assert
    input = "y := x * ?? ; assert y == x * 2;"
    output = "y := x * 2 ;"

    input = "y := x * c1 ; assert y == x * 2;"
    (forall x,y : exits c1 : y := x * c1 -> y == x * 2;)



    input = "y := x * ?? ; assert y == x + x;"
    output = "y := x * 2 ;"

    # simple arithmetic with < and >
    input = "y := x + ?? ; assert y > x;"
    output = "y := x + 1 ;"  # could any number that is greater than 1


    # if condition 1
    input = "y := 0 ; x := ?? ; if x == 5 then ( y := 10 ) ; assert y == 10;"
    output = "y := 0 ; x := 5 ; if x == 5 then ( y := 10 ) ;"




    # multiple variables and arithmetic
    input = " x := 3 ; z := 2 ; t := x + z ; y := x - z + t + ?? ; assert y == 10;"
    output = "x := 3 ; z := 2 ; t := x + z ; y := x - z + t + 6"


    # loops : inside loop hole
    input = " x := 0 ; y := 0;  while x < 10 do ( y := y + ?? )  ; assert y == 10"
