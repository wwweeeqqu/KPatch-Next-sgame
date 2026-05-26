ifndef TARGET_COMPILE
    $(error TARGET_COMPILE not set)
endif

ifndef KP_DIR
    KP_DIR = ../..
endif

CC = $(TARGET_COMPILE)gcc
LD = $(TARGET_COMPILE)ld

INCLUDE_DIRS := . include patch/include linux/include linux/arch/arm64/include linux/tools/arch/arm64/include

INCLUDE_FLAGS := $(foreach dir,$(INCLUDE_DIRS),-I$(KP_DIR)/kernel/$(dir))

objs := sgame_acepeek_v19.o

all: sgame-acepeek-v19.kpm

sgame-acepeek-v19.kpm: ${objs}
	${CC} -r -o $@ $^

# -mno-outline-atomics: gcc 12 emits __aarch64_swp4_sync / __aarch64_ldadd4_sync
#   helpers when atomic ops are present; kernel has no such symbols.
# -fno-tree-loop-distribute-patterns: prevents gcc -O2 from rewriting
#   my_memset/my_memcpy loops back into calls to libc memset/memcpy.
# -fno-builtin-memset/memcpy/strlen: belt-and-suspender against builtin
#   substitution.
EXTRA_CFLAGS := -mno-outline-atomics \
                -fno-tree-loop-distribute-patterns \
                -fno-builtin-memset -fno-builtin-memcpy -fno-builtin-strlen

%.o: %.c
	${CC} $(CFLAGS) $(EXTRA_CFLAGS) $(INCLUDE_FLAGS) -c -O2 -o $@ $<

.PHONY: clean
clean:
	rm -rf *.kpm
	find . -name "*.o" | xargs rm -f
