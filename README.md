# prover
Resolution theorem prover for propositional logic

## disclaimer
This repository is here for the purpose of historical preservation only. The code has been frozen in the state it was turned in.

## usage

### input
Input is a text file with one CNF statement per line, in the following format:

```
x1 x2 x3 ...
```

which means

```
x1 OR x2 OR x3 OR ...
```

You can negate variables with tilde:

```
penguin ~cat ~dolphin
```

Example file:

```
skyIsBlue skyIsOrange
~skyIsOrange
irrelevantVar
~skyIsBlue
```

Make sure you include the negation of the conclusion you're trying to prove.

###output
Each statement is numbered and, for derived statements, the parents are listed.

If a contradiction is found (the proof succeeded), `False` will be the last statement.

## notes
This was a project for my Artificial Intelligence class in 2013.