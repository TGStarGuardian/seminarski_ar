

main: main.o parser.o lexer.o fol.o
	g++ -std=c++2a -o main fol.o main.o parser.o lexer.o

fol.o: fol.cpp fol.hpp

main.o: main.cpp fol.hpp
	g++ -std=c++2a -c -o main.o main.cpp

parser.o: parser.cpp fol.hpp
	g++ -std=c++2a -c -o parser.o parser.cpp

lexer.o: lexer.cpp parser.hpp
	g++ -std=c++2a -c -o lexer.o lexer.cpp

parser.cpp: parser.ypp
	bison -d -o parser.cpp parser.ypp

lexer.cpp: lexer.lpp
	flex -o lexer.cpp lexer.lpp

clean:
	rm -f *.o
	rm -f *~
	rm -f parser.cpp
	rm -f lexer.cpp
	rm -f parser.hpp
	rm -f main
