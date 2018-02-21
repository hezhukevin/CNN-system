EXT_MODULES = src/ext/meow

include $(patsubst %, %/module.make, $(EXT_MODULES))
