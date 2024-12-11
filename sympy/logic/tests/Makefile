# Compiler and flags
CXX = g++
CXXFLAGS = -I/opt/homebrew/Cellar/z3/4.13.3/include
LDFLAGS = -L/opt/homebrew/Cellar/z3/4.13.3/lib -lz3

# Target name
TARGET = blah
SRC = blah.cpp

# Build target
all: $(TARGET)

$(TARGET): $(SRC)
	$(CXX) -o $(TARGET) $(SRC) $(CXXFLAGS) $(LDFLAGS)

# Clean up build files
clean:
	rm -f $(TARGET)
