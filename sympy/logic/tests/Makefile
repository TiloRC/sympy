# Compiler and flags
CXX = g++
CXXFLAGS = -I/opt/homebrew/Cellar/z3/4.13.3/include -I/opt/homebrew/Cellar/gperftools/2.16/include
LDFLAGS = -L/opt/homebrew/Cellar/z3/4.13.3/lib -L/opt/homebrew/Cellar/gperftools/2.16/lib -lz3 -lprofiler -ltcmalloc

# Target name
TARGET = blah
SRC = blah.cpp

# Build target
all: $(TARGET)

$(TARGET): $(SRC)
	arch -x86_64 $(CXX) $(CXXFLAGS) -o $(TARGET) $(SRC) $(LDFLAGS)

# Clean up build files
clean:
	rm -f $(TARGET)
