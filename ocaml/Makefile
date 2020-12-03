CC:=ocamlc

CFLAGS:= -g -I include/
SRC_DIR:= src
OBJ_DIR:= obj
INC_DIR:= include

SRC:= $(wildcard $(SRC_DIR)/*.ml)
INC:= $(wildcard $(INC_DIR)/*.mli)
OBJ:= $(SRC:$(SRC_DIR)/%.ml=$(OBJ_DIR)/%.cmo)

EXEC:= main

.PHONY: all clean

all: $(EXEC)

$(EXEC): $(OBJ)
	$(CC) -o $@ $^

$(OBJ_DIR)/%.cmo: $(SRC)
	$(CC) $(CFLAGS) -c $<

$(OBJ_DIR)/%.cmi: $(INC)
	$(CC) $(CFLAGS) -c $<

$(OBJ_DIR):
	mkdir -p $@

clean: 
	rm -rf *.cmi *.cmo $(EXEC)

config.cmo: config.cmi
while.cmo: while.cmi