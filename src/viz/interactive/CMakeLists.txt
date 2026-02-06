cmake_minimum_required(VERSION 3.16)
project(qbp_proof_viz C)

set(CMAKE_C_STANDARD 11)

# Source files
set(SOURCES
    src/main.c
    src/fonts.c
    src/qphysics.c
    src/proof_graph.c
    src/json_loader.c
    src/scenes/experiment_01_stern_gerlach.c
    lib/cJSON.c
)

if(EMSCRIPTEN)
    # --- WASM build via Emscripten ---
    set(CMAKE_EXECUTABLE_SUFFIX ".html")

    add_executable(index ${SOURCES})

    # raylib is found via emscripten ports or manual path
    if(DEFINED RAYLIB_SRC)
        # Build raylib from source for Emscripten
        add_subdirectory(${RAYLIB_SRC} ${CMAKE_BINARY_DIR}/raylib)
        target_link_libraries(index raylib)
    else()
        # Assume raylib is installed and findable
        find_package(raylib QUIET)
        if(raylib_FOUND)
            target_link_libraries(index raylib)
        else()
            message(FATAL_ERROR
                "raylib not found. Set -DRAYLIB_SRC=/path/to/raylib/source")
        endif()
    endif()

    target_include_directories(index PRIVATE src)

    # Emscripten flags
    set_target_properties(index PROPERTIES
        LINK_FLAGS "--shell-file ${CMAKE_SOURCE_DIR}/shell.html \
                    --preload-file ${CMAKE_SOURCE_DIR}/data@/data \
                    --preload-file ${CMAKE_SOURCE_DIR}/assets@/assets \
                    -sUSE_GLFW=3 \
                    -sASSERTIONS=1 \
                    -sWASM=1 \
                    -sALLOW_MEMORY_GROWTH=1 \
                    -sTOTAL_MEMORY=67108864"
    )

else()
    # --- Native build ---
    add_executable(qbp_proof_viz ${SOURCES})

    find_package(raylib QUIET)
    if(raylib_FOUND)
        target_link_libraries(qbp_proof_viz raylib)
    elseif(DEFINED RAYLIB_SRC)
        add_subdirectory(${RAYLIB_SRC} ${CMAKE_BINARY_DIR}/raylib)
        target_link_libraries(qbp_proof_viz raylib)
    else()
        # Try pkg-config as fallback
        find_package(PkgConfig QUIET)
        if(PkgConfig_FOUND)
            pkg_check_modules(RAYLIB REQUIRED raylib)
            target_include_directories(qbp_proof_viz PRIVATE ${RAYLIB_INCLUDE_DIRS})
            target_link_libraries(qbp_proof_viz ${RAYLIB_LIBRARIES})
            target_link_directories(qbp_proof_viz PRIVATE ${RAYLIB_LIBRARY_DIRS})
        else()
            message(FATAL_ERROR
                "raylib not found. Install raylib or set -DRAYLIB_SRC=/path/to/raylib")
        endif()
    endif()

    target_include_directories(qbp_proof_viz PRIVATE src)

    # Link system libraries needed by raylib on Linux
    if(UNIX AND NOT APPLE)
        target_link_libraries(qbp_proof_viz m GL pthread dl rt X11)
    endif()
endif()
