TO RUN:
install flex bison
commands:
flex lexer.l
bison -d -t parser.y
gcc parser.tab.c
a.exe<quicksort
