CC := gcc
LD := gcc

SRC_DIR := src
OBJ_DIR := obj
BIN_DIR := bin

CFLAGS := -Wall -Wextra -g3 -O3 -Werror -Wshadow -Wconversion -Wdouble-promotion -Wformat=2 -Wformat-truncation=2 -Wundef -fno-common -fstack-usage -Wfloat-equal -Wpointer-arith -Wcast-align -Wstrict-prototypes -Wstrict-overflow=5 -Wwrite-strings -Waggregate-return -ffunction-sections -fdata-sections
LDFLAGS := -Wl,--gc-sections -Wl,--print-gc-sections -pthread

SRC := $(wildcard $(SRC_DIR)/*.c)
OBJ := $(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(SRC))
TARGET := $(patsubst $(SRC_DIR)/%.c, $(BIN_DIR)/%, $(SRC))

all: $(TARGET)

$(TARGET): $(BIN_DIR)/%: $(SRC_DIR)/%.c
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)
	rm -rf *.su

# $(TARGET): $(OBJ)
# 	$(info )
# 	$(info Compilation de increment)
# 	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

# $(OBJ): $(OBJ_DIR)/%.o: $(SRC_DIR)/%.c
# 	$(info )
# 	$(info Compilation des fichiers .o)
# 	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: all clean clean_executable clean_all

clean_all: clean clean_executable

clean:
	$(info Suppression des .su, .o, .h.gch)
	rm -rf $(OBJ_DIR)/*.su $(OBJ_DIR)/*.o

clean_executable:
	$(info Supression des exécutables)
	rm -rf $(TARGET)