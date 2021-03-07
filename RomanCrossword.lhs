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
    | num > 3999 = error "Too big for number system"
    | otherwise = concat [ convertPostion' x | x <- reverse (zip (reverse (show num)) symbols)]

convertPostion' :: (Char, [Char])  -> String
convertPostion' y 
    | x <= 3 =  replicate x lower
    | x == 4 = lower : [mid]
    | x == 5 = [mid]
    | x == 9 = lower : [higher]
    | otherwise = mid : replicate (x - 5) lower
    where (x, symbols) =  (read [fst y] :: Int, snd y)
          (lower, mid, higher) = (symbols !! 0, symbols !! 1, symbols !! 2)

--convertPostion' :: (Char, [Char])  -> String
--convertPostion' y = [fst y]




          
-- convertPostion :: (Ord a) => a -> b -> String 
convertPostion :: Int  -> String
convertPostion num 
    | num <= 3 =  replicate num lower
    | num == 4 = lower : [mid]
    | num == 5 = [mid]
    | num == 9 = lower : [higher]
    | otherwise = mid : replicate (num - 5) lower
    where symbols = ['I', 'V', 'X']
          (lower, mid, higher) = (symbols !! 0, symbols !! 1, symbols !! 2)
   
\end{code}




\begin{code}
bmiTell :: (RealFloat a) => a -> a -> String  
bmiTell weight height  
    | bmi <= 18.5 = "Underweight"  
    | bmi <= 25.0 = "Average"  
    | bmi <= 30.0 = "Overweight"  
    | otherwise   = "Obese"  
    where bmi = weight / height ^ 2 
\end{code}

