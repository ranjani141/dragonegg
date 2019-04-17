GCC		?= $(CC)
CFLAGS	= -g -Wall -Wextra -fPIC -fdump-tree-all
CPATH	=
LIBPATH	=
LDLIBS  =

all: m
	
m:
	$(CC) -o m.o -c $(CFLAGS) $(CPATH) m.f90

clean: 
	rm -rf *.o *.a *.so *.mod *.tu *.class *.original *.gimple *.omplower *.lower *.eh \
		*.cfg *.ompexp *.fixup_cfg1 *.ssa *.fixup_cfg3 *.inline_param1 \
		*.einline *.profile_estimate *.release_ssa *.inline_param2 \
		*.fixup_cfg4 *.oaccdevlow *.veclower *.cplxlower0 *.optimized \
		*.statistics *.dot *.png *-hello hello a.out
