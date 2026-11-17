# ----------------------------
# Makefile Options
# ----------------------------

NAME = TAPROOT
DESCRIPTION = "taproot polynomial cas"
COMPRESSED = NO

CFLAGS = -Wall -Wextra -Oz -fno-inline
CXXFLAGS = -Wall -Wextra -Oz

# ----------------------------

include $(shell cedev-config --makefile)

check:
	mkdir -p obj
	cc -std=c99 -Wall -Wextra -g -fsanitize=address,undefined -fno-sanitize-recover=undefined src/cas.c test/test.c -o obj/check
	obj/check

SIMFLAGS = -std=c99 -Wall -Wextra -g -fsanitize=address,undefined -I test/host -idirafter $(shell cedev-config --prefix)/include

obj/sim/run: src/main.c src/cas.c src/cas.h test/sim.c test/host/graphx.h
	mkdir -p obj/sim
	cc $(SIMFLAGS) -Dmain=sim_main -c src/main.c -o obj/sim/main.o
	cc $(SIMFLAGS) -c src/cas.c -o obj/sim/cas.o
	cc $(SIMFLAGS) -c test/sim.c -o obj/sim/sim.o
	cc -fsanitize=address,undefined obj/sim/main.o obj/sim/cas.o obj/sim/sim.o -o $@
