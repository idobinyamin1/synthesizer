
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
    #(forall x,y : exits c1 : y := x * c1 -> y == x * 2;)

    input = "y := x * ?? ; assert y == x + x;"
    output = "y := x * 2 ;"


    # multiple variables and arithmetic
    input = " x := 3 ; z := 2 ; t := x + z ; y := t + ?? ; assert y == 10;"
    output = "x := 3 ; z := 2 ; t := x + z ; y := x + 5"

    # simple arithmetic with < and >
    input = "y := x + ?? ; assert y > x;"
    output = "y := x + 1 ;"  # could any number that is greater than 1


    # if condition 1 - hole in the beginning
    input = "y := 0 ; x := ?? ; if x == 5 then ( y := 10 ) ; assert y == 10;"
    output = "y := 0 ; x := 5 ; if x == 5 then ( y := 10 ) ;"

    # if condition 2 - hole in the condition body
    input = "y := 10  ; if x == 5 then ( y := ?? ) ; assert y == 10;"
    output = "y := 10  ; if x == 5 then ( y := 10 ) ;"

    # if condition 3 - hole inside the condition body
    input = "y := 0 ; x = 5 ; if x == ?? then ( y := 10 ) ; assert y == 10;"


    # if else
    input = "y := 0 ; x := ?? ; if x == 5 then ( y := 10 ) else ( y := 20 ) ; assert y == 10;"


    # loops : hole at the beginning
    input = " x := 0 ; t := ??;  while x < t do ( y := y + 1 )  ; assert y == 10"
    output = " x := 0 ; t := 10;  while x < t do ( y := y + 1 )  ; assert y == 10"

    # loops : hole at the while condition
    input = " y := 0 ; while y < ?? do ( y := y + 1 )  ; assert y == 10"
    output = " y := 0 ; while y < 10 do ( y := y + 1 )  ; assert y == 10"

    # loops : hole at the while body
    input = " y := 0 ; while y < 10 do ( y := y + ?? )  ; assert y == 10"
    output = " y := 0 ; while y < 10 do ( y := y + 1 )  ; assert y == 10"

    # multiple holes
    input = " x := 0 ; y := 0 ; while y < ?? do ( y := y + ?? )  ; assert y == 10"
    output = " x := 0 ; y := 0 ; while y < 10 do ( y := y + 1 )  ; assert y == 10"

    # multiple holes 2
    input = " x := ?? ; z := ?? ; y := x + z ; assert y == 10"
    output = " x := 5 ; z := 5 ; y := x + z ; assert y == 10"  # x and z can be any numbers that adds up to 10


    # multiple holes 3
    input = "y := 0 ; x := ?? ; if x == 5 then ( y := y + ?? ) else ( y := 20 ) ; assert y == 10;"
    output = "y := 0 ; x := 5 ; if x == 5 then ( y := y + 10 ) else ( y := 20 ) ; assert y == 10;"