configure_file(lit.site.cfg.in lit.site.cfg.in2 @ONLY)
file(GENERATE
     OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
     INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.in2)

add_test(NAME test-verilog
        COMMAND lit ${LIT_ARGS} .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
)
