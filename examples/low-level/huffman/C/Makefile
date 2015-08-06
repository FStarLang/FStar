HUFFMAN_OBJS = huffman.o utilities.o 
HUFFMAN_EXE = huffman

$(HUFFMAN_EXE): $(HUFFMAN_OBJS)
	$(CC) -o $@ $^ 

%.o:	%.c
	$(CC) -c $< -o $@

clean:
	$(RM) *.o $(HUFFMAN_OBJS) $(HUFFMAN_EXE) test_data