all:	exact heuristic

exact:
	javac tw/exact/*.java

heuristic:
	javac tw/heuristic/*.java

clean: 
	rm tw/*/*.class