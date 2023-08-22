
def test():

    # feature

    # basic test input is x and output is y in the format of (x,y)
    examples = ((1,1), (2,2), (3,3))
    input = "y := ?? ;"
    output = "y := x ;"

    # simple arithmetic
    examples = ((1,6), (2,7), (5,10))
    input = "y := x + ?? ;"
    output = "x := 5 ; y := x + 5"

    examples = ((1,2), (2,4), (5,10))
    input = "y := x * ?? ;"
    output = "y := x * 2 ;"


    # multiple variables and arithmetic
    examples = ((1,3), (4,9), (5,11), (6,13)) # should be y = 2x + 1
    input = " z := 2 ; t := x + z ; y := x - z + t + ?? ; assert y == 10;" # y = x - 2 +x + 2 = 2x + ??
    output = "x := 3 ; z := 2 ; t := x + z ; y := x - z + t + 1"


    # if condition 1 - hole in the beginning
    examples = ( (5,10), (1,2), (2,2) )
    input = "y := ?? ; if x == 5 then ( y := 10 ) ;"
    output = "y := 2 ; if x == 5 then ( y := 10 ) ;"

    # if condition 2 - hole in the condition body
    input = "y := 10  ; if x == 5 then ( y := ?? ) ;"
    output = "y := 10  ; if x == 5 then ( y := 10 ) ;"


    # if else
    examples = ((5,10), (1,20), (2,20))
    input = " if x == 5 then ( y := ?? ) else ( y := 20 ) ;"
    output = " if x == 5 then ( y := 10 ) else ( y := 20 ) ;"


    # loops : hole at the beginning
    examples = ((1,1), (2,2), (3,3))
    input = " y := 0;  while y < x do ( y := y + ?? )  ; "
    output = " y := 0;  while y < x do ( y := y + 1 )  ; "

    # loops : hole at the while condition
    examples = ((1,1), (2,2), (3,3))
    input = " y := ?? ; while y < x do ( y := y + 1 )  ; "
    output = " y := 0;  while y < x do ( y := y + 1 )  ; "

    # multiple holes
    examples = ((1,4), (2,3), (3,2))
    input = " y := 0 ; while x < ?? do ( y := y + ?? )  ; "
    output = "  y := 0 ; while x < 5 do ( y := y + 1 ) ;"

    # multiple holes 2
    examples = ((1,6), (2,7), (3,8))
    input = " z := ?? ; y := x + z ; "
    output = " z := 5 ; y := x + z ;"


    # multiple holes 3
    examples = ((5,10), (1,20), (2,20))
    input = "y := 0 ; if x == 5 then ( y := ?? ) else ( y := ?? ) ;"
    output = "y := 0 ; if x == 5 then ( y := 10 ) else ( y := 20 ) ;"