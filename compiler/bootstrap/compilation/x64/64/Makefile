# To support large stack+heap, use -mcmodel=medium.
# CFLAGS += -mcmodel=medium

# To set the stack and heap available to the CakeML compiler,
# also edit the .space directives in cake.S.

# To set the stack and heap directives available to your own
# CakeML programs, use the --stack_size and --heap_size
# command-line arguments to the CakeML compiler.

# Build the CakeML compiler.
cake: cake.o basis_ffi.o

# A simple example showing how to build your program (input.cml)
# using CakeML.
result.S: input.cml cake
	./cake <$< >$@

result: result.o basis_ffi.o
