CFLAGS = -g `epic -includedirs`

go: bittwiddle.o
	idris ResIO.idr

bittwiddle.o: bittwiddle.h bittwiddle.c

