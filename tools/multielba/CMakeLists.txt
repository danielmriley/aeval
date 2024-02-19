add_executable (multielba MultiBoundSolver.cpp)
target_link_libraries (multielba ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS multielba RUNTIME DESTINATION bin)
