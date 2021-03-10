\begin{code}
import Data.List
import Data.Function
\end{code}

ghci RomanCrossword.lhs

PART 0

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

convertToNumeral :: Int -> String
convertToNumeral num 
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
upperBound = fst (last [(x, numeral) | x <- [500..1899], let numeral = convertToNumeral x, 'M' `elem` numeral  && 'D' `elem` numeral])
\end{code}

Running this, we see that 1899 is infact the larget number as it contains both 'M' and 'D' symbols ("MDCCCXCIX").
N.b. could make this better by checking that M occurs only once.


3. Bounded Primes

For this problem the 'Sieve of Eratosthenes' is used to filter identify primes. 
Turner (1975) is attributed to defining a functional implemention of the Sieve. 
In the Sieve algorithm, whenever a prime is identify all multiples of that prime can
be removed ('sieved') out of the search space for possible primes, as it is known that they are 
divisable by the at least the identified prime. 

Turner's implemention has been shown to be suboptimal asymtopically (https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf).
Indeed, O'Neill (2009), brands the implemention as the 'unfaithful Sieve' arguing it is not an accurate 
translation of the Seive as described by Eratosthenes (due to how the non-primes are elimated immediately after primes are found, 
rather than lazily and starting from the primes' square and working back towards the prime (O'Neill (2009))). 

O'Neill instead presents the 'genuine Seive of Eratosthenes' as follows, (n.b. this is slightly altered to handle x <= 1):

\begin{code}
primes = 2 : [x | x <- [3..], isprime x]
isprime x 
    | x <= 1 = False
    | otherwise = all (\p -> x `mod` p > 0) (factorsToTry x)
    where factorsToTry x = takeWhile (\p -> p*p <= x) primes
\end{code}

algorithm works as follows:

primes := the list of all numbers which satify the predicate `isprime`
isprime:= Uses `all` and a lambda function to check that all values `p` of the iterable `factorsToTry` modulo x are greater 1.
factorsToTry:= uses a takewhile loop to iterate all ps in primes that are <= x, starting from p squared.
E.g. factorsToTry 17 is equal to [2,3]. 

This is a beautiful implemention in haskell as both `primes` and `factorsToTry` reference each other in their definitions, meaning that
the lazy evaluation properties of haskell are put to optimum use as the `primes` infinite list is being dynamically evaluated up to x just 
at the point it is required for computation.

-- TODO: Maybe reimplement the algo?

https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
https://wiki.haskell.org/index.php?title=Prime_numbers&oldid=36858#Postponed_Filters_Sieve

\begin{code}
data Roman = Roman String deriving (Show)
type Pair = (Int, Roman) -- TODO: make work with Integer as per spec!

boundedPrimes :: [Pair]
boundedPrimes = [(x, Roman (convertToNumeral x)) | x <- [2..upperBound], isprime x]

\end{code}

4. Numeral Length

\begin{code}


n1', n2', n3', n4', n5', n6', n7', n8' :: [Int]
n1' = integerOfNumeralLength 1
n2' = integerOfNumeralLength 2
n3' = integerOfNumeralLength 3
n4' = integerOfNumeralLength 4
n5' = integerOfNumeralLength 5
n6' = integerOfNumeralLength 6
n7' = integerOfNumeralLength 7
n8' = integerOfNumeralLength 8
n9' = integerOfNumeralLength 9


p1', p2', p3', p4', p5', p6', p7', p8', p9' :: [Pair]
p1' = numeralsOfLength 1
p2' = numeralsOfLength 2
p3' = numeralsOfLength 3
p4' = numeralsOfLength 4
p5' = numeralsOfLength 5
p6' = numeralsOfLength 6
p7' = numeralsOfLength 7
p8' = numeralsOfLength 8
p9' = numeralsOfLength 9

-- Note these all have the additional ' as they are redefined below.

integerOfNumeralLength :: Int -> [Int]
integerOfNumeralLength x = [fst x | x <- numeralsOfLength x]

numerals = take 3999 [numeral | x <- [1..], let numeral = convertToNumeral x]
numeralsOfLength :: Int -> [Pair]
numeralsOfLength x 
    | x == 0 = []
    | x > 3999 = []
    | otherwise = [(i, Roman numeral) | i <- [1..upperBound], let numeral = convertToNumeral i, length numeral == x && isprime i]
\end{code}


This implemention works fine, however the issue with it is that for any value of i all numerals are checked. We could say that
it is not really in the spirit of haskell, as the `numerals` list is greedily computed and exhaustively checked everytime the `numeralsOfLength`
function is called. A better solution is to lazily group the numerals by their length and then retrieve just the relevent grouping.

This can be refactored using sortBy, GroupBy and on as follows: 

\begin{code}
numeralsOfLength' :: Int -> [(Int, String)]
numeralsOfLength' x = pairs !! (x -1)
    where pairs = groupBy ((==) `on` (length . snd)) (sortBy (compare`on` (length . snd)) nums)
          nums = [(i, numeral) | i <- [1..upperBound], let numeral = convertToNumeral i, isprime i]
\end{code}


This is an improvement as we now group all numerals together and then just return the x-1 position (because of zero indexing)
for a given x, rather than exhaustively checking up to upperbound for any x, but currently it an [(Int, String) ] not a [Pair].

A further refactor is required to make this return a Pair:

\begin{code}
numeralsOfLength'' :: Int -> [Pair]
numeralsOfLength'' x = pairs !! (x -1)
    where pairs = groupBy ((==) `on` (length' . snd)) (sortBy (compare`on` (length' . snd)) boundedPrimes)
--          length' = (\_ x -> length x)

length' :: Roman -> Int
length' (Roman x) = length x
\end{code}

Note, we have to implement a custom length' function to work  on numerals, this  is because the type signature 
for the inbuilt length is `length :: Foldable t => t a -> Int`. As the Roman type is not 
a foldable, we need handle only running length on the numeral String of the Roman, not the Roman itself. Attempting to do so results in: 
` Couldn't match expected type ‘[a0]’ with actual type ‘Roman’` 
https://stackoverflow.com/questions/33394756/haskell-function-length-doesnt-work-with-custom-data-type

There is a further improvement here to reuse `boundedPrimes` rather than calculate the prime pairs on the fly.

If we can now put this together (p1, n1... p9, n9) type annotations for the improved function above.

\begin{code}

nl = numeralsOfLength''

n1, n2, n3, n4, n5, n6, n7, n8 :: [Int]
n1 = inl 1
n2 = inl 2
n3 = inl 3
n4 = inl 4
n5 = inl 5
n6 = inl 6
n7 = inl 7
n8 = inl 8
n9 = inl 9


p1, p2, p3, p4, p5, p6, p7, p8, p9 :: [Pair]
p1 = nl 1
p2 = nl 2
p3 = nl 3
p4 = nl 4
p5 = nl 5
p6 = nl 6
p7 = nl 7
p8 = nl 8
p9 = nl 9

inl :: Int -> [Int]
inl x = [fst x | x <- nl x]

\end{code}

PART 1

5. Equation 6 - two letter primes for a,b 

Given we know that a, b are two character primes we need to find all the possible permutations of the 
two character primes. 

p2 = [(2,Roman "II"),(11,Roman "XI"),(101,Roman "CI")]

\begin{code}
enum = zip [0..] n2
ab = [(snd x, convertToNumeral (snd x), snd (enum !! i), convertToNumeral (snd (enum !! i))) | x <- enum, i <- [0..(length enum -1)], fst x /= i]
\end{code}

The algorithm makes use of the `zip` function with `n2` from step 4 produce a numbering of the items in 
`n2`. This approach was based on the `enumerate` concept in python, in which an iterable, x can be enumerated 
to yield each item and and index for every index in the length of x. 

E.g.

`enum = zip [0..] n2` yields the following list of tuples: `[(0,2),(1,11),(2,101)]`, where the first index is the ith position of `[0..]`

We then can iterate enum (as 'x'), and a range up to the length of enum-1 (as 'i'). The predicate `fst x /= i`
is used to guard against adding combinations of the same item, when collecting tuples of `snd x, snd (enum !! i)`
on the left side of the list comprehension. 

Running this we can see the possible values for a,b are: 
[("II","XI"),("II","CI"),("XI","II"),("XI","CI"),("CI","II"),("CI","XI")]

This can be made a bit more reusable by wrapping it in a function that takes the n-iterable to enumerate, where n is the length of the numeral. 

\begin{code}
candidatePairs :: [Int] -> [(Int, String, Int, String)]
candidatePairs [] = []
candidatePairs (x:xs) = [(snd x, convertToNumeral (snd x), snd (enum !! i), convertToNumeral (snd (enum !! i))) | x <- enum, i <- [0..(length enum -1)], fst x /= i]
    where enum = zip [0..] (x:xs)
\end{code}

6. s,t possible values

One way to approach solving this is to iterate the possible values of b -a from step 5, and then compare the difference to the deltas of n9. 
For example, the first two positions of `n9` are [283,337], assuming t > 3, the difference is 54, meaning that is there is an a-b combination = 54 
this combination would satify the equation.




