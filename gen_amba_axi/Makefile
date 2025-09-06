#-----------------------------------------------------------------------------
SHELL		= /bin/sh
MAKEFILE	= Makefile

#-------------------------------------------------------------
ARCH	= $(shell uname)
MACH	= $(shell uname -m)
ifeq ($(ARCH),Linux)
  PLATFORM= linux
  GCC=gcc
  ifeq ($(MACH),x86_64)
        PLATFORMX= linux64
        INSTD=../../bin/linux64
  else
        PLATFORMX= linux32
        INSTD=../../bin/linux32
  endif
else ifeq ($(findstring CYGWIN_NT,$(ARCH)),CYGWIN_NT)
  PLATFORM= cygwin
  GCC=i686-w64-mingw32-gcc
  ifeq ($(MACH),x86_64)
        PLATFORMX= cygwin64
        INSTD=../../bin/win64
  else
        PLATFORMX= cygwin32
        INSTD=../../bin/win32
  endif
else ifeq ($(findstring MINGW,$(ARCH)),MINGW)
  PLATFORM= mingw
  GCC=gcc
  ifeq ($(MACH),x86_64)
        PLATFORMX= mingw64
        INSTD=../../bin/win64
  else
        PLATFORMX= mingw32
        INSTD=../../bin/win32
  endif
else
  $(info un-supported platform $(ARCH))
endif

#-------------------------------------------------------------
CC              = gcc
DEFS            =
INCDIRS         = -Isrc
LIBS            = -lm
ifeq ($(PLATFORM),cygwin)
DEFS            += -DWIN32
LIBS            +=
else ifeq ($(PLATFORM),mingw)
DEFS            += -DWIN32
LIBS            +=
endif
OPT             = -g
CCFLAGS         = $(DEFS) $(OPT)

#-------------------------------------------------------------
TARGET		= gen_amba_axi

SRC	=\
	main.c\
	arg_parser.c\
	gen_axi_amba.c\
	gen_axi_utils.c\
	gen_axi_mtos.c\
	gen_axi_stom.c\
	gen_axi_arbiter_mtos.c\
	gen_axi_arbiter_stom.c\
	gen_axi_default_slave.c\
	gen_axi_wid.c\
	gen_axi_qos.c\
	gen_axi_firewall.c\
	gen_axi_firewall_optimized.c\
	gen_axi_cdc.c\
	gen_axi_ace_lite.c\
	gen_axi_region.c\
	gen_axi_optimized.c\
	gen_axi_verilog_optimized.c\
	gen_axi_pipeline.c\
	gen_axi_user_wrapper.c\
	gen_axi_modular.c\
	gen_axi_fifo.c\
	gen_axi_validation.c\
	ace_lite/coherency/gen_ace_lite_coherency_controller.c\
	ace_lite/coherency/gen_ace_lite_snoop_filter.c\
	ace_lite/coherency/gen_ace_lite_barrier_sync.c\
	ace_lite/coherency/gen_ace_lite_domain_manager.c\
	ace_lite/coherency/gen_ace_lite_cache_states.c\
	ace_lite/coherency/gen_ace_lite_exclusive_monitor.c\
	ace_lite/coherency/gen_ace_lite_signal_arbiter.c\
	ace_lite/cache_ops/gen_ace_lite_cache_ops.c\
	ace_lite/interconnect/gen_ace_lite_interconnect.c\
	ace_lite/dvm/gen_ace_lite_dvm_controller.c\
	ace_lite/dvm/gen_ace_lite_tlb_manager.c\
	ace_lite/system/gen_ace_lite_system_coordinator.c
		
OBJS	= $(SRC:.c=.o)

#-------------------------------------------------------------
H_DIR		= src
C_DIR		= src

vpath %.h	$(H_DIR)
vpath %.c	$(C_DIR)

#-------------------------------------------------------------
OBJECTDIR = obj
DUMMY      := $(shell [ -d $(OBJECTDIR) ] || mkdir $(OBJECTDIR) )
DUMMY      := $(shell [ -d $(OBJECTDIR)/ace_lite/coherency ] || mkdir -p $(OBJECTDIR)/ace_lite/coherency )
DUMMY      := $(shell [ -d $(OBJECTDIR)/ace_lite/cache_ops ] || mkdir -p $(OBJECTDIR)/ace_lite/cache_ops )
DUMMY      := $(shell [ -d $(OBJECTDIR)/ace_lite/interconnect ] || mkdir -p $(OBJECTDIR)/ace_lite/interconnect )
DUMMY      := $(shell [ -d $(OBJECTDIR)/ace_lite/dvm ] || mkdir -p $(OBJECTDIR)/ace_lite/dvm )
DUMMY      := $(shell [ -d $(OBJECTDIR)/ace_lite/system ] || mkdir -p $(OBJECTDIR)/ace_lite/system )

#-------------------------------------------------------------
$(OBJECTDIR)/%.o: %.c
	$(CC) -c $(CCFLAGS) $(INCDIRS) -o $@ $<

#-------------------------------------------------------------
all: $(TARGET)

$(TARGET): $(addprefix $(OBJECTDIR)/, $(OBJS))
	$(CC) -o $(TARGET) $^ $(LIBS)

run: $(TARGET)
	./$(TARGET) --master=2 --slave=3 --output=amba_axi_m2s3.v

#-------------------------------------------------------------
install: $(TARGET)
	@if [ ! -d $(INSTD) ]; then mkdir -p $(INSTD); fi
	cp $(TARGET) $(INSTD)/$(TARGET)
	chmod +x $(INSTD)/$(TARGET)

#-------------------------------------------------------------
DIRS	= $(subst /,, $(dir $(wildcard */Makefile)))

clean:
	-rm -fr $(OBJECTDIR)
	-rm -fr ./Debug
	-rm -f *.stackdump
	-rm -f compile.log
	-rm -f *.v
	for D in $(DIRS); do\
		if [ -f $$D/Makefile ] ; then \
			echo "make -C $$D -s $@";\
			make -C $$D -s $@;\
		fi;\
	done

cleanup clobber: clean
	-rm -f $(TARGET) $(TARGET).exe
	for D in $(DIRS); do\
		if [ -f $$D/Makefile ] ; then \
			echo "make -C $$D -s $@";\
			make -C $$D -s $@;\
		fi;\
	done

cleanupall distclean: cleanup
	for D in $(DIRS); do\
		if [ -f $$D/Makefile ] ; then \
			echo "make -C $$D -s $@";\
			make -C $$D -s $@;\
		fi;\
	done
