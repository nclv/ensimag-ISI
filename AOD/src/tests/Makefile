CC = gcc
LD = gcc
INCLUDE = ../../includes
INCLUDES = -I$(INCLUDE)

# -O0 désactive les optimisations à la compilation
# C'est utile pour débugger, par contre en "production"
# on active au moins les optimisations de niveau 2 (-O2).
CFLAGS = -std=c99 -Wall -Wextra -g3 -O3 -Werror -Wshadow -Wconversion -Wdouble-promotion -Wformat=2 -Wformat-truncation=2 -Wundef -fno-common -fstack-usage -fstack-protector-all -Wfloat-equal -Wpointer-arith -Wcast-align -Wstrict-prototypes -Wstrict-overflow=5 -Wwrite-strings -Waggregate-return -ffunction-sections -fdata-sections  -fopenmp -lm
LDFLAGS = -Wl,--gc-sections -Wl,--print-gc-sections -Wl,-z,relro,-z,now -fopenmp -lm

BINDIR = ../../bin/
OBJDIR = ../../obj/

COMMON_OBJ_FILES = $(OBJDIR)utils.o $(OBJDIR)timing.o

EXEC_NAMES = test_transposition test_merge_sort test_parcours_tableau_bidimensionnel test_filtre_multi-pas
EXEC_FILES = $(addprefix $(BINDIR), $(EXEC_NAMES))

all: $(EXEC_FILES)

$(BINDIR)%: $(OBJDIR)%.o
	$(LD) $(LDFLAGS) $(INCLUDES) $< $(subst test_,,$<) $(COMMON_OBJ_FILES) -o $@
	$(info )
	$(info Call gcc to generate $@ from $<)

$(OBJDIR)%.o: %.c
	$(CC) -c $(CFLAGS) $(INCLUDES) $< -o $@
	$(info )
	$(info Call gcc to generate $@ from $<)