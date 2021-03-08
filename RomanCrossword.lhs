ghci RomanCrossword.lhs


Symbol	I	V	X	L	C	D	M
Value	1	5	10	50	100	500	1000

1. Convert Roman numerals to any positive integer up to 3999

The solution is based on the realisation that Roman numerals can be viewed as a 
point between lower, mid and upper symbols, where the magnatude of the number defines
the subset of symbols. From this we can see the following pattern is always obeyed in the
standard system:  (L)+++-M+++-H. Where L, M, H are a subset of symbols from set of numerals. 
This can also be written as 

N<3  | N=4  | N=5 | N<9 & N>5 | N=9
L*N, |LM,   | M   | M+(d*L)   | L-H, 

N is the number being converted, and d := the difference between the number and 
the mid point of the range (i.e. 5).

N.b. In contiguous magnatudes, the L of the second set is neccasarliy the H of the preceeding set. 

When viewed in this way we can see that the numeral symbols can be grouped with the magnatude for 
which they are bounds as follows: 

Units: "IVX"
Tens: "XLC"
Hundreds: "CDM"
Thousands: "M"

Note, that thousands only has a lower bound, hence the invarient that 3999 is the largest number that 
can be represented in this system. 

The elegance of this number system is that the L*N, LM, M, M + (d*L) L-H desribed above holds at the 
micro and macro level, meaning that we can utalise it to convert every digit of a number, and then simply contatonate the results 
back together E.g. 

24 = Tens 2, units 4 
Tens 1 = 2 * Lower bound for tens = XX
Units = 4 = Mid bound - lower bound for units = IV
24 = XXIV

The below algorithm does exactly this, namely: 

0. If N > 3999 error,
1.  Zip the reversed number with the corresponding subset of numerals. (n.b. `show` is used here to allow reversal of an int by first representing it as a string )
    -- e.g. given N = 123, this zip would yield
    [(3, "CDM"), (2, "XLC"), (1, "IVX")]
2. Via a list comprehension, pass each tuple of this list to be converted (using `convertPostion` function), where `convertPostion` Implements the  L*N, LM, M, M + (d*L) L-H conversion pattern.
    -- e.g. ["C", "XX", "III"]
3. Concatonate the resulting list of Strings together for the final output: 
    -- e.g. "CXXIII"

\begin{code}

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

\end{code}

2. Upperbound

To find the upperbound a simple bruteforce approach was used. 
The lower bound for the search is  1000 as this is the first ocurence of "M". We also know that the 
upper bound for search is 1899, as 1900 is "MDM" and so doesn't satify the condition of only one ocurence of "M".
We can also deduce that largest number will contain one "M" and one "D", as there can only be one "D" in the numeral before 
moving into the next 1000 range.

\begin{code}
upperBound = fst (last [(x, numeral) | x <- [500..1899], let numeral = convertToNumerial x, 'M' `elem` numeral  && 'D' `elem` numeral])
\end{code}

Running this, we see that 1899 is infact the larget number as it contains both 'M' and 'D' symbols ("MDCCCXCIX").



