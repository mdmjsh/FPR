ghci RomanCrossword.lhs


Symbol	I	V	X	L	C	D	M
Value	1	5	10	50	100	500	1000

1. Convert Roman numerals to any positive integer up to 3999
Because strings are lists, we can use list comprehensions to process and produce strings. 

\begin{code}
--symbols = "IVXLCDM"
symbols = ["IVX","XLC","CDM","M"]


convertToNumerial :: Int -> String
convertToNumerial num 
    | num > 3999 = error "Too big for number system!"
    | otherwise = concat [ convertPostion x | x <- reverse (zip (reverse (show num)) symbols)]

convertPostion :: (Char, [Char])  -> String
convertPostion y 
    | x <= 3 =  replicate x lower
    | x == 4 = lower : [mid]
    | x == 5 = [mid]
    | x == 9 = lower : [higher]
    | otherwise = mid : replicate (x - 5) lower
    where (x, symbols) =  (read [fst y] :: Int, snd y)
          (lower, mid, higher) = (symbols !! 0, symbols !! 1, symbols !! 2)

