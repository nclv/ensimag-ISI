EXE=arith1 div0 div1 mult linear_search min_sort

.PHONY: help all clean 

help:
	@echo "\"make <binary>\" where <binary> is among:"
	@echo "   $(EXE)"
	@echo "or \"make all\" to compile all"

all: $(EXE)

arith%: arith%.c any.o Makefile
	gcc -Wall $< any.o -o $@

mult: mult.c Makefile
	gcc -Wall $< -o $@

div0: div0.c any.o Makefile
	gcc -Wall $< any.o -o $@

div1: div1.c any.o Makefile
	gcc -Wall $< any.o -o $@

linear_search: linear_search.c any.o Makefile
	gcc -Wall $< any.o -o $@

min_sort: min_sort.c any.o Makefile
	gcc -Wall $< any.o -o $@

%.o: %.c %.h Makefile
	gcc -Wall -c $<

clean:
	$(RM) *~ *.o $(EXE)
