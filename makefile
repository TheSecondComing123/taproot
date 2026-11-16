# ----------------------------
# Makefile Options
# ----------------------------

NAME = TAPROOT
DESCRIPTION = "taproot polynomial cas"
COMPRESSED = NO

CFLAGS = -Wall -Wextra -Oz
CXXFLAGS = -Wall -Wextra -Oz

# ----------------------------

include $(shell cedev-config --makefile)

check:
	mkdir -p obj
	cc -std=c99 -Wall -Wextra -g -fsanitize=address,undefined -fno-sanitize-recover=undefined src/cas.c test/test.c -o obj/check
	obj/check
