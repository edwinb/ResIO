CFLAGS = -g `epic -includedirs`

go: bittwiddle.o rawnet.o
	idris ResIO.idr

bittwiddle.o: bittwiddle.h bittwiddle.c
rawnet.o: rawnet.h rawnet.c

