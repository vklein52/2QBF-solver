cmake_minimum_required(VERSION 3.10)
project(Research)

set(CMAKE_CXX_STANDARD 11)

add_executable(Research main.cpp cmake-build-debug/Formulas/Formula.cpp cmake-build-debug/Formulas/Formula.h cmake-build-debug/Formulas/AndFormula.cpp cmake-build-debug/Formulas/AndFormula.h cmake-build-debug/Formulas/OrFormula.cpp cmake-build-debug/Formulas/OrFormula.h cmake-build-debug/Formulas/NotFormula.cpp cmake-build-debug/Formulas/NotFormula.h cmake-build-debug/Formulas/VarFormula.cpp cmake-build-debug/Formulas/VarFormula.h cmake-build-debug/Formulas/ClauseVar.cpp cmake-build-debug/Formulas/ClauseVar.h cmake-build-debug/Formulas/FormulaHelper.cpp Formulas/FormulaHelper.h)
