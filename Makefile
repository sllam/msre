
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))

PY_EXEC  := python
CPP_EXEC := mpiCC

MSRE_SRC_PATH := $(CURDIR)
MSRE_COMPILER_PATH := ${MSRE_SRC_PATH}/compiler/msrex
MSRE_RUNTIME_PATH := ${MSRE_SRC_PATH}/runtime

MSRE_LIB_PATH := /usr/local/lib
MSRE_BIN_PATH := /usr/local/bin
MSRE_TEMP_BUILD_PATH := ${MSRE_SRC_PATH}/temp

install:
	echo "Emptying temp directories (if exists)..."
	rm -rf msre_lib
	rm -rf ${MSRE_LIB_PATH}/msre_lib 
	rm -f ${MSRE_BIN_PATH}/msre.conf
	echo "Building MSRE compiler..."
	cd ${MSRE_COMPILER_PATH} ; ${PY_EXEC} setup.py install
	echo "Creating MSRE library..."
	mkdir msre_lib
	mkdir msre_lib/cpp
	cp ${MSRE_COMPILER_PATH}/msre.py msre_lib/.
	cp -r ${MSRE_RUNTIME_PATH}/msre msre_lib/cpp/.
	echo "Copying MSRE library to ${MSRE_LIB_PATH}"
	mv msre_lib ${MSRE_LIB_PATH}/.
	echo "Copying MSRE executable to ${MSRE_BIN_PATH}"
	cp msre ${MSRE_BIN_PATH}/.
	echo 'MSRE_LIB_PATH=${MSRE_LIB_PATH}/msre_lib' >> ${MSRE_BIN_PATH}/msre.conf
	echo 'PY_EXEC=${PY_EXEC}' >> ${MSRE_BIN_PATH}/msre.conf
	echo 'CPP_EXEC=${CPP_EXEC}' >> ${MSRE_BIN_PATH}/msre.conf

clean:
	rm -rf msre_lib
	rm -rf ${MSRE_COMPILER_PATH}/build
	rm -rf ${MSRE_COMPILER_PATH}/msrex/*.pyc
	rm -rf ${MSRE_COMPILER_PATH}/msrex/*/*.pyc
	rm -rf ${MSRE_COMPILER_PATH}/msrex/*/*/*.pyc
	rm -rf ${MSRE_COMPILER_PATH}/msrex/*/*/*/*.pyc


