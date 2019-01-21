SRC_FILES := $(wildcard src/main/scala/**.scala)

all: build.sbt $(SRC_FILES)
	sbt package
