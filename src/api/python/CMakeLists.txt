find_package(PythonExtensions REQUIRED)
find_package(Cython REQUIRED)

include_directories(${PYTHON_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_LIST_DIR})        # btorapi.pxd
include_directories(${CMAKE_CURRENT_LIST_DIR}/../..)  # boolector.h
include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(generated_file "${CMAKE_CURRENT_BINARY_DIR}/pyboolector_options.pxd")

# Generate pyboolector_options.pxd from btortypes.h
add_custom_target(
  pyboolector_options
  ALL
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/mkoptions.py"
    "${CMAKE_CURRENT_LIST_DIR}/../../btortypes.h"
    "${generated_file}"
  DEPENDS
    mkoptions.py
  COMMENT
    "Generate pyboolector_options.pxd"
)
add_cython_target(pyboolector CXX)  # implicitely uses pyboolector.pyx

add_library(pyboolector
            MODULE
            ${pyboolector} boolector_py.c pyboolector_abort.cpp)
add_dependencies(pyboolector pyboolector_options)

target_link_libraries(pyboolector boolector ${LIBRARIES} ${PYTHON_LIBRARIES})
python_extension_module(pyboolector)
