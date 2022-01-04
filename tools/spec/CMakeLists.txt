add_executable (spechorn BoundSolver.cpp)
target_link_libraries (spechorn ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
install(TARGETS spechorn RUNTIME DESTINATION bin)
