All: buildAstPractice 

removeDotO:
	rm main.o astp.o

compileAll:
	clang++ `llvm-config-17 --cxxflags --ldflags --libs` main.o astp.o -o main_exec

buildMain:
	clang++ main.cpp `llvm-config-17 --cxxflags --ldflags --libs` -o main.o
buildAstPractice:
	clang++-17 -std=c++17 $(llvm-config-17 --cxxflags) -I/usr/lib/llvm-17/include \
	AstPractice.cpp $(llvm-config-17 --ldflags --libs all --system-libs) \
	-L/usr/lib/llvm-17/lib -lclangTooling -lclangFrontend -lclangAST -lclangBasic -lclangDriver -lclangSerialization

Something:
	g++ asp.o 	$(llvm-config-17 --ldflags --libs all --system-libs) -L/usr/lib/llvm-17/lib -lclangTooling -lclangFrontend -lclangAST -lclangBasic -lclangSerialization -o main_exec
	-I/usr/lib/llvm-17/include \
	AstPractice.cpp $(llvm-config-17 --ldflags --libs all --system-libs) \
	-L/usr/lib/llvm-17/lib -lclangTooling.a -lclangFrontend.a -lclangAST.a -lclangBasic.a -lclangSerialization.a
	
  