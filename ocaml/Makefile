CC:=ocamlc

CFLAGS:= -g
SRC_DIR:= src
OBJ_DIR:= obj
INC_DIR:= include

SRC:= $(wildcard $(SRC_DIR)/*.ml)
INC:= $(wildcard $(INC_DIR)/*.mli)
OBJ:= $(SRC:$(SRC_DIR)/%.ml=$(OBJ_DIR)/%.cmo)

EXEC:= main

.PHONY: all clean

all: $(OBJ_DIR) $(EXEC)

$(EXEC): $(OBJ_DIR)/while.cmo $(OBJ_DIR)/config.cmo $(OBJ_DIR)/main.cmo
	$(CC) -o $@ $^

$(OBJ_DIR)/main.cmo: $(SRC_DIR)/main.ml $(OBJ_DIR)/config.cmi $(OBJ_DIR)/while.cmi 
	$(CC) -c $(CFLAGS) $< -I $(OBJ_DIR) -o $@

$(OBJ_DIR)/config.cmo: $(SRC_DIR)/config.ml $(OBJ_DIR)/while.cmi $(OBJ_DIR)/config.cmi
	$(CC) -c $(CFLAGS) $< -I $(OBJ_DIR) -o $@

$(OBJ_DIR)/while.cmo: $(SRC_DIR)/while.ml $(OBJ_DIR)/while.cmi
	$(CC) -c $(CFLAGS) $< -I $(OBJ_DIR) -o $@

$(OBJ_DIR)/while.cmi: $(INC_DIR)/while.mli
	$(CC) -c $(CFLAGS) $< -I $(OBJ_DIR) -o $@

$(OBJ_DIR)/config.cmi: $(INC_DIR)/config.mli $(OBJ_DIR)/while.cmi
	$(CC) -c $(CFLAGS) $< -I $(OBJ_DIR) -o $@

$(OBJ_DIR):
	mkdir -p $@

clean: 
	rm -rf *.cmi *.cmo $(EXEC) $(OBJ_DIR)
