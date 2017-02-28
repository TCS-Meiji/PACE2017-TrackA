all:	exact heuristic

exact:
	javac tw/exact/*

heuristic:
	javac tw/heuristic/*

clean: 
	rm tw/*/*.class